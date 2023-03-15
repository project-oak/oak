//
// Copyright 2022 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

//! Wasm business logic provider based on [Wasmi](https://github.com/paritytech/wasmi).

#![no_std]

extern crate alloc;

#[cfg(test)]
extern crate std;

#[cfg(test)]
mod tests;

use alloc::{boxed::Box, format, sync::Arc, vec::Vec};
use byteorder::{ByteOrder, LittleEndian};
use hashbrown::HashMap;
use oak_functions_abi::{
    proto::{ExtensionHandle, OakStatus},
    Request, Response, StatusCode,
};
use oak_functions_extension::{ExtensionFactory, OakApiNativeExtension};
use oak_logger::{Level, OakLogger};
use wasmi::{AsContext, AsContextMut, Func, Memory, MemoryType, Store};

pub const MAIN_FUNCTION_NAME: &str = "main";
pub const ALLOC_FUNCTION_NAME: &str = "alloc";
pub const MEMORY_NAME: &str = "memory";

// Needs to be consistent with definition of the Wasm import module in the Oak Functions ABI.
const OAK_FUNCTIONS: &str = "oak_functions";

// Type aliases for positions and offsets in Wasm linear memory. Any future 64-bit version
// of Wasm would use different types.
pub type AbiPointer = u32;
pub type AbiPointerOffset = u32;
// Type alias for the ExtensionHandle type, which has to be cast into a ExtensionHandle.
pub type AbiExtensionHandle = i32;

pub struct UserState<L: OakLogger> {
    request_bytes: Vec<u8>,
    response_bytes: Vec<u8>,
    extensions: HashMap<ExtensionHandle, Box<dyn OakApiNativeExtension>>,
    logger: L,
}

impl<L> UserState<L>
where
    L: OakLogger,
{
    // We initialize user state with the empty response.
    fn init(
        request_bytes: Vec<u8>,
        extensions: HashMap<ExtensionHandle, Box<dyn OakApiNativeExtension>>,
        logger: L,
    ) -> Self {
        UserState {
            request_bytes,
            response_bytes: Vec::new(),
            extensions,
            logger,
        }
    }

    pub fn get_extension(
        &mut self,
        handle: i32,
    ) -> Result<&mut Box<dyn OakApiNativeExtension>, OakStatus> {
        let handle: ExtensionHandle = ExtensionHandle::from_i32(handle).ok_or_else(|| {
            self.log_error(&format!("failed to convert handle {:?} from i32.", handle));
            OakStatus::ErrInvalidHandle
        })?;

        let extensions = &mut self.extensions;
        let logger = &self.logger;

        extensions.get_mut(&handle).ok_or_else(|| {
            logger.log_sensitive(
                Level::Error,
                &format!("can't find extension with handle {:?}.", handle),
            );
            OakStatus::ErrInvalidHandle
        })
    }

    fn log_error(&self, message: &str) {
        self.logger.log_sensitive(Level::Error, message)
    }
}

impl<L> alloc::fmt::Debug for UserState<L>
where
    L: OakLogger,
{
    fn fmt(&self, formatter: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        formatter
            .debug_struct("UserState")
            .field("request_bytes", &self.request_bytes)
            .field("response_bytes", &self.response_bytes)
            .field("extensions", &self.extensions)
            .finish()
    }
}

/// `WasmState` holds runtime values for a particular execution instance of Wasm, handling a
/// single user request. The methods here correspond to the ABI OAK_FUNCTIONS functions that allow
/// the Wasm module to exchange the request and the response with the Oak functions server. These
/// functions translate values between Wasm linear memory and Rust types.
// TODO(#3796): Remove WasmState.
pub struct WasmState<L: OakLogger> {
    instance: wasmi::Instance,
    store: wasmi::Store<UserState<L>>,
}

impl<L> WasmState<L>
where
    L: OakLogger,
{
    pub fn new(
        module: Arc<wasmi::Module>,
        request_bytes: Vec<u8>,
        logger: L,
        extensions: HashMap<ExtensionHandle, Box<dyn OakApiNativeExtension>>,
    ) -> anyhow::Result<Self> {
        let user_state = UserState::init(request_bytes, extensions, logger);
        // For isolated requests we need to create a new store for every request.
        let mut store = wasmi::Store::new(module.engine(), user_state);
        let linker = OakLinker::new(module.engine(), &mut store);
        let (instance, store) = linker.instantiate(store, module)?;
        // TODO(#3785): Add logging and list exports.
        let wasm_state = Self { instance, store };
        Ok(wasm_state)
    }

    // Invokes the Wasm module by calling main.
    fn invoke(&mut self) {
        let main = self
            .instance
            .get_typed_func::<(), ()>(&self.store, MAIN_FUNCTION_NAME)
            .expect("couldn't get `main` export");
        let result = main.call(&mut self.store, ());
        self.store.data().logger.log_sensitive(
            Level::Info,
            &format!("running Wasm module completed with result: {:?}", result),
        );
    }

    // Needed for unit tests.
    #[allow(dead_code)]
    fn get_request_bytes(&self) -> Vec<u8> {
        let user_state = self.store.data();
        user_state.request_bytes.clone()
    }

    fn get_response_bytes(&self) -> Vec<u8> {
        let user_state = self.store.data();
        user_state.response_bytes.clone()
    }
}

// Exports the functions from oak_functions_abi/src/lib.rs.
struct OakLinker<L: OakLogger> {
    linker: wasmi::Linker<UserState<L>>,
}

impl<L> OakLinker<L>
where
    L: OakLogger,
{
    fn new(engine: &wasmi::Engine, store: &mut Store<UserState<L>>) -> Self {
        let mut linker: wasmi::Linker<UserState<L>> = wasmi::Linker::new(engine);

        // Add memory to linker.
        // TODO(#3783): Find a sensible value for initial pages.
        let initial_pages = 100;
        let memory_type =
            MemoryType::new(initial_pages, None).expect("failed to define Wasm memory type");
        let memory =
            wasmi::Memory::new(store, memory_type).expect("failed to initialize Wasm memory");
        linker
            .define(OAK_FUNCTIONS, MEMORY_NAME, wasmi::Extern::Memory(memory))
            .expect("failed to define Wasm memory in linker");

        linker
            .func_wrap(
                OAK_FUNCTIONS,
                "read_request",
                // The types in the signatures correspond to the parameters from
                // oak_functions_abi/src/lib.rs.
                // TODO(#3797): Simplify wrapped functions.
                |mut caller: wasmi::Caller<'_, UserState<L>>,
                 buf_ptr_ptr: AbiPointer,
                 buf_len_ptr: AbiPointer| {
                    let result = read_request(&mut caller, buf_ptr_ptr, buf_len_ptr);
                    from_oak_status(result)
                },
            )
            .expect("failed to define read_request in linker");

        linker
            .func_wrap(
                OAK_FUNCTIONS,
                "write_response",
                // The types in the signatures correspond to the parameters from
                // oak_functions_abi/src/lib.rs.
                |mut caller: wasmi::Caller<'_, UserState<L>>,
                 buf_ptr: AbiPointer,
                 buf_len: AbiPointerOffset| {
                    let result = write_response(&mut caller, buf_ptr, buf_len);
                    from_oak_status(result)
                },
            )
            .expect("failed to define write_response in linker");

        linker
            .func_wrap(
                OAK_FUNCTIONS,
                "invoke",
                // The types in the signatures correspond to the parameters from
                // oak_functions_abi/src/lib.rs.
                |mut caller: wasmi::Caller<'_, UserState<L>>,
                 handle: AbiExtensionHandle,
                 request_ptr: AbiPointer,
                 request_len: AbiPointerOffset,
                 response_ptr_ptr: AbiPointer,
                 response_len_ptr: AbiPointer| {
                    let result = invoke_extension(
                        &mut caller,
                        handle,
                        request_ptr,
                        request_len,
                        response_ptr_ptr,
                        response_len_ptr,
                    );
                    from_oak_status(result)
                },
            )
            .expect("failed to define invoke in linker");
        OakLinker { linker }
    }

    /// Instantiates the Oak Linker and checks whether the instance exports `main`, `alloc` and a
    /// memory is attached.
    ///
    /// Use the same store used when creating the linker.
    fn instantiate(
        self,
        mut store: Store<UserState<L>>,
        module: Arc<wasmi::Module>,
    ) -> anyhow::Result<(wasmi::Instance, Store<UserState<L>>)> {
        let instance = self
            .linker
            .instantiate(&mut store, &module)
            .map_err(|err| anyhow::anyhow!("failed to instantiate Wasm module: {:?}", err))?
            // Use `main` as entry point.
            .ensure_no_start(&mut store)
            .map_err(|err| {
                anyhow::anyhow!("failed to ensure no start in Wasm module: {:?}", err)
            })?;

        // Check that the instance exports "main".
        let _ = &instance
            .get_typed_func::<(), ()>(&store, MAIN_FUNCTION_NAME)
            .expect("couldn't validate `main` export");

        // Check that the instance exports "alloc".
        let _ = &instance
            .get_typed_func::<i32, AbiPointer>(&store, ALLOC_FUNCTION_NAME)
            .expect("couldn't validate `alloc` export");

        // Make sure that non-empty `memory` is attached to the instance. Fail early if
        // `memory` is not available.
        instance
            .get_memory(&store, MEMORY_NAME)
            .ok_or(anyhow::anyhow!("couldn't find Wasm `memory` export"))?;

        Ok((instance, store))
    }
}

/// Reads the buffer starting at address `buf_ptr` with length `buf_len` from the Wasm memory.
pub fn read_buffer(
    ctx: &mut impl AsContext,
    memory: &mut wasmi::Memory,
    buf_ptr: AbiPointer,
    buf_len: AbiPointerOffset,
) -> Result<Vec<u8>, OakStatus> {
    let mut target = alloc::vec![0; buf_len as usize];

    let buf_ptr = buf_ptr
        .try_into()
        .expect("failed to convert AbiPointer to usize as required by wasmi API");
    memory.read(ctx, buf_ptr, &mut target).map_err(|_err| {
        // TODO(#3785): Add logging, which needs access to logger in the user state.
        // We don't have access in ctx, so we either need to pass the logger as argument or
        // think of a different refactoring.
        // ctx.data().log_error(
        //   &format!("Unable to read buffer from guest memory: {:?}", err),
        // );
        OakStatus::ErrInvalidArgs
    })?;
    Ok(target)
}

///  Writes the u32 `value` at the `address` of the Wasm memory.
pub fn write_u32(
    ctx: &mut impl AsContextMut,
    memory: &mut wasmi::Memory,
    value: u32,
    address: AbiPointer,
) -> Result<(), OakStatus> {
    let value_bytes = &mut [0; 4];
    LittleEndian::write_u32(value_bytes, value);
    write_buffer(ctx, memory, value_bytes, address).map_err(|_err| {
        // TODO(#3785): Add logging, which needs access to logger in the user state.
        // We don't have access in ctx, so we either need to pass the logger as argument or
        // think of a different refactoring.
        // ctx.data().log_error(
        //    &format!("Unable to write u32 value into guest memory: {:?}", err),
        // );
        OakStatus::ErrInvalidArgs
    })
}

/// Writes the buffer `source` at the address `dest` of the Wasm memory, if `source` fits in the
/// allocated memory.
pub fn write_buffer(
    ctx: &mut impl AsContextMut,
    memory: &mut wasmi::Memory,
    source: &[u8],
    dest: AbiPointer,
) -> Result<(), OakStatus> {
    let dest = dest
        .try_into()
        .expect("failed to convert AbiPointer to usize as required by wasmi API");
    memory.write(ctx, dest, source).map_err(|_err| {
        // TODO(#3785): Add logging, which needs access to logger in the user state.
        // We don't have access in ctx, so we either need to pass the logger as argument or
        // think of a different refactoring.
        // ctx.data().log_error(
        //    &format!("Unable to write buffer into guest memory: {:?}", err),
        // );
        OakStatus::ErrInvalidArgs
    })
}

/// Writes the given `buffer` by allocating `buffer.len()` Wasm memory and writing the address
/// of the allocated memory to `dest_ptr_ptr` and the length to `dest_len_ptr`.
pub fn alloc_and_write_buffer(
    ctx: &mut impl AsContextMut,
    memory: &mut wasmi::Memory,
    alloc: Func,
    buffer: Vec<u8>,
    dest_ptr_ptr: AbiPointer,
    dest_len_ptr: AbiPointer,
) -> Result<(), OakStatus> {
    let len = buffer.len() as i32;
    // Call alloc.

    // Will hold address where memory of size len was allocated, initialized with -1.
    let mut address = [wasmi::Value::I32(-1)];
    alloc
        .call(
            ctx.as_context_mut(),
            &[wasmi::Value::I32(len)],
            &mut address,
        )
        .expect("`alloc` call failed");
    let dest_ptr = match address[0] {
        // Assumes 32-bit Wasm addresses.
        wasmi::Value::I32(v) => v
            .try_into()
            .map_or_else(|_| Err(OakStatus::ErrInternal), Ok),
        _ => Err(OakStatus::ErrInternal),
    }?;

    // Write to buffer.
    write_buffer(ctx, memory, &buffer, dest_ptr)?;
    write_u32(ctx, memory, dest_ptr, dest_ptr_ptr)?;
    write_u32(ctx, memory, buffer.len() as u32, dest_len_ptr)?;
    Ok(())
}

/// Corresponds to the OAK_FUNCTIONS ABI function [`read_request`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#read_request).
pub fn read_request<L: OakLogger>(
    caller: &mut wasmi::Caller<'_, UserState<L>>,
    dest_ptr_ptr: AbiPointer,
    dest_len_ptr: AbiPointer,
) -> Result<(), OakStatus> {
    let alloc = get_exported_alloc(caller)?;
    let mut memory = get_exported_memory(caller)?;
    let request_bytes = caller.data().request_bytes.clone();

    alloc_and_write_buffer(
        caller,
        &mut memory,
        alloc,
        request_bytes,
        dest_ptr_ptr,
        dest_len_ptr,
    )
}

/// Corresponds to the OAK_FUNCTIONS ABI function [`write_response`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#write_response).
pub fn write_response<L: OakLogger>(
    caller: &mut wasmi::Caller<'_, UserState<L>>,
    buf_ptr: AbiPointer,
    buf_len: AbiPointerOffset,
) -> Result<(), OakStatus> {
    let mut memory = get_exported_memory(caller)?;
    caller.data_mut().response_bytes = read_buffer(caller, &mut memory, buf_ptr, buf_len)?;
    Ok(())
}

pub fn invoke_extension<L: OakLogger>(
    caller: &mut wasmi::Caller<'_, UserState<L>>,
    handle: i32,
    request_ptr: AbiPointer,
    request_len: AbiPointerOffset,
    response_ptr_ptr: AbiPointer,
    response_len_ptr: AbiPointer,
) -> Result<(), OakStatus> {
    let alloc = get_exported_alloc(caller)?;

    let mut memory = get_exported_memory(caller)?;

    let request = read_buffer(caller, &mut memory, request_ptr, request_len).map_err(|err| {
        caller.data().log_error(&format!(
            "Handle {:?}: Unable to read input from guest memory: {:?}",
            handle, err
        ));
        OakStatus::ErrInvalidArgs
    })?;

    let user_state = caller.data_mut();
    let extension = user_state.get_extension(handle)?;
    let response = extension.invoke(request)?;

    alloc_and_write_buffer(
        caller,
        &mut memory,
        alloc,
        response,
        response_ptr_ptr,
        response_len_ptr,
    )
}

// Helper function to get exported MEMORY from caller.
fn get_exported_memory<L: OakLogger>(
    caller: &mut wasmi::Caller<'_, UserState<L>>,
) -> Result<Memory, OakStatus> {
    let ext = caller.get_export(MEMORY_NAME).ok_or_else(|| {
        caller
            .data()
            .log_error(&format!("failed to get exported {}", MEMORY_NAME));
        OakStatus::ErrInternal
    })?;

    ext.into_memory().ok_or_else(|| {
        caller
            .data()
            .log_error(&format!("exported {} is not a memory", MEMORY_NAME));
        OakStatus::ErrInternal
    })
}

// Helper function to get exported ALLOC_FUNCTION_NAME from caller.
fn get_exported_alloc<L: OakLogger>(
    caller: &mut wasmi::Caller<'_, UserState<L>>,
) -> Result<Func, OakStatus> {
    let ext = caller.get_export(ALLOC_FUNCTION_NAME).ok_or_else(|| {
        caller
            .data()
            .log_error(&format!("failed to get exported {}", ALLOC_FUNCTION_NAME));
        OakStatus::ErrInternal
    })?;

    ext.into_func().ok_or_else(|| {
        caller
            .data()
            .log_error(&format!("exported {} is not a func", ALLOC_FUNCTION_NAME));
        OakStatus::ErrInternal
    })
}

// An ephemeral request handler with a Wasm module for handling the requests.
#[derive(Clone)]
pub struct WasmHandler<L: OakLogger> {
    wasm_module: Arc<wasmi::Module>,
    extension_factories: Arc<Vec<Box<dyn ExtensionFactory<L>>>>,
    logger: L,
}

impl<L> WasmHandler<L>
where
    L: OakLogger,
{
    pub fn create(
        wasm_module_bytes: &[u8],
        extension_factories: Vec<Box<dyn ExtensionFactory<L>>>,
        logger: L,
    ) -> anyhow::Result<Self> {
        let engine = wasmi::Engine::default();
        let module = wasmi::Module::new(&engine, wasm_module_bytes)
            .map_err(|err| anyhow::anyhow!("couldn't load module from buffer: {:?}", err))?;

        Ok(WasmHandler {
            wasm_module: Arc::new(module),
            extension_factories: Arc::new(extension_factories),
            logger,
        })
    }

    fn init_wasm_state(&self, request_bytes: Vec<u8>) -> anyhow::Result<WasmState<L>> {
        let mut extensions = HashMap::new();

        // Create an extension from every factory.
        for factory in self.extension_factories.iter() {
            let extension = factory.create()?;
            extensions.insert(extension.get_handle(), extension);
        }

        let wasm_state = WasmState::new(
            self.wasm_module.clone(),
            request_bytes,
            self.logger.clone(),
            extensions,
        )?;

        Ok(wasm_state)
    }

    pub fn handle_invoke(&self, request: Request) -> anyhow::Result<Response> {
        let response_bytes = self.handle_raw_invoke(request.body)?;
        Ok(Response::create(StatusCode::Success, response_bytes))
    }

    /// Handles an invocation using raw bytes and returns the response as raw bytes.
    pub fn handle_raw_invoke(&self, request_bytes: Vec<u8>) -> anyhow::Result<Vec<u8>> {
        let mut wasm_state = self.init_wasm_state(request_bytes)?;

        wasm_state.invoke();

        wasm_state
            .store
            .data_mut()
            .extensions
            .values_mut()
            .try_for_each(|e| e.terminate())?;

        Ok(wasm_state.get_response_bytes())
    }
}

/// A helper function to move between our specific result type `Result<(), OakStatus>` and the
/// `wasmi` specific result type `Result<i32, wasmi::Trap>`.
fn from_oak_status(result: Result<(), OakStatus>) -> Result<i32, wasmi::core::Trap> {
    let oak_status = result.err().unwrap_or(OakStatus::Ok);
    Ok(oak_status as i32)
}
