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
mod tests;

use alloc::{boxed::Box, format, sync::Arc, vec::Vec};
use anyhow::Context;
use byteorder::{ByteOrder, LittleEndian};
use hashbrown::HashMap;
use oak_functions_abi::{
    proto::{ExtensionHandle, OakStatus},
    Request, Response, StatusCode,
};
use oak_functions_extension::{ExtensionFactory, OakApiNativeExtension};
use oak_logger::{Level, OakLogger};
use wasmi::ValueType;

const MAIN_FUNCTION_NAME: &str = "main";
const ALLOC_FUNCTION_NAME: &str = "alloc";

/// Wasm host function index numbers for `wasmi` to map import names with. This numbering is not
/// exposed to the Wasm client. See <https://docs.rs/wasmi/0.6.2/wasmi/trait.Externals.html>
const READ_REQUEST: usize = 0;
const WRITE_RESPONSE: usize = 1;
const INVOKE: usize = 4;

// Type aliases for positions and offsets in Wasm linear memory. Any future 64-bit version
// of Wasm would use different types.
pub type AbiPointer = u32;
pub type AbiPointerOffset = u32;
// Type alias for the ExtensionHandle type, which has to be cast into a ExtensionHandle.
pub type AbiExtensionHandle = i32;
/// Wasm type identifier for position/offset values in linear memory. Any future 64-bit version of
/// Wasm would use a different value.
pub const ABI_USIZE: ValueType = ValueType::I32;

/// `WasmState` holds runtime values for a particular execution instance of Wasm, handling a
/// single user request. The methods here correspond to the ABI host functions that allow the Wasm
/// module to exchange the request and the response with the Oak functions server. These functions
/// translate values between Wasm linear memory and Rust types.
pub struct WasmState<L: OakLogger> {
    request_bytes: Vec<u8>,
    response_bytes: Vec<u8>,
    instance: Option<wasmi::ModuleRef>,
    memory: Option<wasmi::MemoryRef>,
    logger: L,
    extensions: HashMap<ExtensionHandle, Box<dyn OakApiNativeExtension>>,
}

impl<L> WasmState<L>
where
    L: OakLogger,
{
    pub fn new(
        module: &wasmi::Module,
        request_bytes: Vec<u8>,
        logger: L,
        extensions: HashMap<ExtensionHandle, Box<dyn OakApiNativeExtension>>,
    ) -> anyhow::Result<Self> {
        let mut abi = Self {
            request_bytes,
            response_bytes: Vec::new(),
            instance: None,
            memory: None,
            logger,
            extensions,
        };

        let instance = wasmi::ModuleInstance::new(
            module,
            &wasmi::ImportsBuilder::new().with_resolver("oak_functions", &abi),
        )
        .map_err(|err| anyhow::anyhow!("failed to instantiate Wasm module: {:?}", err))?
        .assert_no_start();

        check_export_function_signature(
            &instance,
            MAIN_FUNCTION_NAME,
            &wasmi::Signature::new(&[][..], None),
        )
        .context("could not validate `main` export")?;
        check_export_function_signature(
            &instance,
            ALLOC_FUNCTION_NAME,
            &wasmi::Signature::new(&[ValueType::I32][..], Some(ValueType::I32)),
        )
        .context(" could not validate `alloc` export")?;

        abi.instance = Some(instance.clone());
        // Make sure that non-empty `memory` is attached to the WasmState. Fail early if
        // `memory` is not available.
        abi.memory = Some(
            instance
                .export_by_name("memory")
                .context("could not find Wasm `memory` export")?
                .as_memory()
                .cloned()
                .context("could not interpret Wasm `memory` export as memory")?,
        );

        Ok(abi)
    }

    fn invoke(&mut self) {
        let instance = self.instance.as_ref().expect("no instance").clone();
        let result = instance.invoke_export(MAIN_FUNCTION_NAME, &[], self);
        self.logger.log_sensitive(
            Level::Info,
            &format!("Running Wasm module completed with result: {:?}", result),
        );
    }

    fn get_response_bytes(&self) -> Vec<u8> {
        self.response_bytes.clone()
    }

    /// Helper function to get memory.
    pub fn get_memory(&self) -> &wasmi::MemoryRef {
        self.memory
            .as_ref()
            .expect("WasmState memory not attached!?")
    }

    /// Validates whether a given address range (inclusive) falls within the currently allocated
    /// range of guest memory.
    fn validate_range(&self, addr: AbiPointer, offset: AbiPointerOffset) -> Result<(), OakStatus> {
        let memory_size: wasmi::memory_units::Bytes = self.get_memory().current_size().into();
        // Check whether the end address is below or equal to the size of the guest memory.
        if wasmi::memory_units::Bytes((addr as usize) + (offset as usize)) <= memory_size {
            Ok(())
        } else {
            Err(OakStatus::ErrInvalidArgs)
        }
    }

    /// Reads the buffer starting at address `buf_ptr` with length `buf_len` from the Wasm memory.
    pub fn read_buffer_from_wasm_memory(
        &self,
        buf_ptr: AbiPointer,
        buf_len: AbiPointerOffset,
    ) -> Result<Vec<u8>, OakStatus> {
        self.get_memory()
            .get(buf_ptr, buf_len as usize)
            .map_err(|err| {
                self.logger.log_sensitive(
                    Level::Error,
                    &format!("Unable to read buffer from guest memory: {:?}", err),
                );
                OakStatus::ErrInvalidArgs
            })
    }

    /// Writes the buffer `source` at the address `dest` of the Wasm memory, if `source` fits in the
    /// allocated memory.
    pub fn write_buffer_to_wasm_memory(
        &self,
        source: &[u8],
        dest: AbiPointer,
    ) -> Result<(), OakStatus> {
        self.validate_range(dest, source.len() as u32)?;
        self.get_memory().set(dest, source).map_err(|err| {
            self.logger.log_sensitive(
                Level::Error,
                &format!("Unable to write buffer into guest memory: {:?}", err),
            );
            OakStatus::ErrInvalidArgs
        })
    }

    ///  Writes the u32 `value` at the `address` of the Wasm memory.
    pub fn write_u32_to_wasm_memory(
        &self,
        value: u32,
        address: AbiPointer,
    ) -> Result<(), OakStatus> {
        let value_bytes = &mut [0; 4];
        LittleEndian::write_u32(value_bytes, value);
        self.get_memory().set(address, value_bytes).map_err(|err| {
            self.logger.log_sensitive(
                Level::Error,
                &format!("Unable to write u32 value into guest memory: {:?}", err),
            );
            OakStatus::ErrInvalidArgs
        })
    }

    //// Read the u32 value at the `address` from the Wasm memory.
    pub fn read_u32_from_wasm_memory(&self, address: AbiPointer) -> Result<u32, OakStatus> {
        let address = self.get_memory().get(address, 4).map_err(|err| {
            self.logger.log_sensitive(
                Level::Error,
                &format!("Unable to read u32 value from guest memory: {:?}", err),
            );
            OakStatus::ErrInvalidArgs
        })?;
        Ok(LittleEndian::read_u32(&address))
    }

    /// Writes the given `buffer` by allocating `buffer.len()` Wasm memory and writing the address
    /// of the allocated memory to `dest_ptr_ptr` and the length to `dest_len_ptr`.
    pub fn alloc_and_write_buffer_to_wasm_memory(
        &mut self,
        buffer: Vec<u8>,
        dest_ptr_ptr: AbiPointer,
        dest_len_ptr: AbiPointer,
    ) -> Result<(), OakStatus> {
        let dest_ptr = self.alloc(buffer.len() as u32);
        self.write_buffer_to_wasm_memory(&buffer, dest_ptr)?;
        self.write_u32_to_wasm_memory(dest_ptr, dest_ptr_ptr)?;
        self.write_u32_to_wasm_memory(buffer.len() as u32, dest_len_ptr)?;
        Ok(())
    }

    /// Corresponds to the host ABI function [`read_request`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#read_request).
    pub fn read_request(
        &mut self,
        dest_ptr_ptr: AbiPointer,
        dest_len_ptr: AbiPointer,
    ) -> Result<(), OakStatus> {
        let dest_ptr = self.alloc(self.request_bytes.len() as u32);
        self.write_buffer_to_wasm_memory(&self.request_bytes, dest_ptr)?;
        self.write_u32_to_wasm_memory(dest_ptr, dest_ptr_ptr)?;
        self.write_u32_to_wasm_memory(self.request_bytes.len() as u32, dest_len_ptr)?;
        Ok(())
    }

    /// Corresponds to the host ABI function [`write_response`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#write_response).
    pub fn write_response(
        &mut self,
        buf_ptr: AbiPointer,
        buf_len: AbiPointerOffset,
    ) -> Result<(), OakStatus> {
        let response = self
            .get_memory()
            .get(buf_ptr, buf_len as usize)
            .map_err(|err| {
                self.logger.log_sensitive(
                    Level::Error,
                    &format!(
                        "write_response(): Unable to read name from guest memory: {:?}",
                        err
                    ),
                );
                OakStatus::ErrInvalidArgs
            })?;
        self.response_bytes = response;
        Ok(())
    }

    pub fn invoke_extension(
        &mut self,
        handle: AbiExtensionHandle,
        request_ptr: AbiPointer,
        request_len: AbiPointerOffset,
        response_ptr_ptr: AbiPointer,
        response_len_ptr: AbiPointer,
    ) -> Result<(), OakStatus> {
        let handle: ExtensionHandle = ExtensionHandle::from_i32(handle).ok_or_else(|| {
            self.log_error(&format!("Fail to convert handle {:?} from i32.", handle));
            OakStatus::ErrInvalidHandle
        })?;

        let request = self
            .read_buffer_from_wasm_memory(request_ptr, request_len)
            .map_err(|err| {
                self.log_error(&format!(
                    "Handle {:?}: Unable to read input from guest memory: {:?}",
                    handle, err
                ));
                OakStatus::ErrInvalidArgs
            })?;

        let extension = match self.extensions.get_mut(&handle) {
            // Can't convince the borrow checker to use `ok_or_else` to `self.log_error`.
            Some(extension) => Ok(extension),
            None => {
                self.log_error(&format!("Cannot find extension with handle {:?}.", handle));
                Err(OakStatus::ErrInvalidHandle)
            }
        }?;

        let response = extension.invoke(request)?;
        self.alloc_and_write_buffer_to_wasm_memory(response, response_ptr_ptr, response_len_ptr)
    }

    pub fn alloc(&mut self, len: u32) -> AbiPointer {
        let result = self.instance.as_ref().unwrap().invoke_export(
            ALLOC_FUNCTION_NAME,
            &[wasmi::RuntimeValue::I32(len as i32)],
            // When calling back into `alloc` we don't need to expose any of the rest of the ABI
            // methods.
            &mut wasmi::NopExternals,
        );
        let result_value = result
            .expect("`alloc` call failed")
            .expect("no value returned from `alloc`");
        match result_value {
            wasmi::RuntimeValue::I32(v) => v as u32,
            _ => panic!("invalid value type returned from `alloc`"),
        }
    }

    fn log_error(&self, message: &str) {
        self.logger.log_sensitive(Level::Error, message)
    }
}

impl<L> wasmi::Externals for WasmState<L>
where
    L: OakLogger,
{
    /// Invocation of a host function specified by its registered index. Acts as a wrapper for
    /// the relevant native function, just:
    /// - checking argument types (which should be correct as `wasmi` will only pass through those
    ///   types that were specified when the host function was registered with `resolve_func`).
    /// - mapping resulting return/error values.
    fn invoke_index(
        &mut self,
        index: usize,
        args: wasmi::RuntimeArgs,
    ) -> Result<Option<wasmi::RuntimeValue>, wasmi::Trap> {
        match index {
            READ_REQUEST => from_oak_status_result(
                self.read_request(args.nth_checked(0)?, args.nth_checked(1)?),
            ),
            WRITE_RESPONSE => from_oak_status_result(
                self.write_response(args.nth_checked(0)?, args.nth_checked(1)?),
            ),
            INVOKE => from_oak_status_result(self.invoke_extension(
                args.nth_checked(0)?,
                args.nth_checked(1)?,
                args.nth_checked(2)?,
                args.nth_checked(3)?,
                args.nth_checked(4)?,
            )),
            _ => {
                // Here https://paritytech.github.io/wasmi/wasmi/trait.Externals.html#examples panics with
                //  panic!("Unimplemented function at {}.", index)
                // We prefer not to panic, and trap in an unreachable state instead.
                Err(wasmi::Trap::new(wasmi::TrapKind::Unreachable))
            }
        }
    }
}

impl<L> wasmi::ModuleImportResolver for WasmState<L>
where
    L: OakLogger,
{
    fn resolve_func(
        &self,
        field_name: &str,
        signature: &wasmi::Signature,
    ) -> Result<wasmi::FuncRef, wasmi::Error> {
        // Look for the function (i.e., `field_name`) in the statically registered functions.
        let (index, expected_signature) =
            oak_functions_resolve_func(field_name).ok_or_else(|| {
                wasmi::Error::Instantiation(format!("Export {} not found", field_name))
            })?;

        if signature == &expected_signature {
            Ok(wasmi::FuncInstance::alloc_host(expected_signature, index))
        } else {
            Err(wasmi::Error::Instantiation(format!(
                "Export `{}` doesn't match expected signature; got: {:?}, expected: {:?}",
                field_name, signature, expected_signature
            )))
        }
    }
}

fn check_export_function_signature(
    instance: &wasmi::ModuleInstance,
    export_name: &str,
    expected_signature: &wasmi::Signature,
) -> anyhow::Result<()> {
    let export_function = instance
        .export_by_name(export_name)
        .context("could not find Wasm export")?
        .as_func()
        .cloned()
        .context("could not interpret Wasm export as function")?;
    if export_function.signature() != expected_signature {
        anyhow::bail!(
            "invalid signature for export: {:?}, expected: {:?}",
            export_function.signature(),
            expected_signature
        );
    } else {
        Ok(())
    }
}

// An ephemeral request handler with a Wasm module for handling the requests.
#[derive(Clone)]
pub struct WasmHandler<L: OakLogger> {
    // Wasm module to be served on each invocation. `Arc` is needed to make `WasmHandler`
    // cloneable.
    module: Arc<wasmi::Module>,
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
        let module = wasmi::Module::from_buffer(&wasm_module_bytes)
            .map_err(|err| anyhow::anyhow!("could not load module from buffer: {:?}", err))?;

        Ok(WasmHandler {
            module: Arc::new(module),
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

        let wasm_state =
            WasmState::new(&self.module, request_bytes, self.logger.clone(), extensions)?;

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
            .extensions
            .values_mut()
            .try_for_each(|e| e.terminate())?;

        Ok(wasm_state.get_response_bytes())
    }
}

/// A resolver function, mapping `oak_functions` host function names to an index and a type
/// signature.
fn oak_functions_resolve_func(field_name: &str) -> Option<(usize, wasmi::Signature)> {
    // The types in the signatures correspond to the parameters from
    // oak_functions/abi/src/lib.rs
    let (index, expected_signature) = match field_name {
        "read_request" => (
            READ_REQUEST,
            wasmi::Signature::new(
                &[
                    ABI_USIZE, // buf_ptr_ptr
                    ABI_USIZE, // buf_len_ptr
                ][..],
                Some(ValueType::I32),
            ),
        ),
        "write_response" => (
            WRITE_RESPONSE,
            wasmi::Signature::new(
                &[
                    ABI_USIZE, // buf_ptr
                    ABI_USIZE, // buf_len
                ][..],
                Some(ValueType::I32),
            ),
        ),
        "invoke" => (
            INVOKE,
            wasmi::Signature::new(
                &[
                    ABI_USIZE, // handle
                    ABI_USIZE, // request_ptr
                    ABI_USIZE, // request_len
                    ABI_USIZE, // response_ptr_ptr
                    ABI_USIZE, // response_len_ptr
                ][..],
                Some(ValueType::I32),
            ),
        ),
        _ => return None,
    };

    Some((index, expected_signature))
}

/// A helper function to move between our specific result type `Result<(), OakStatus>` and the
/// `wasmi` specific result type `Result<Option<wasmi::RuntimeValue>, wasmi::Trap>`, mapping:
/// - `Ok(())` to `Ok(Some(OakStatus::Ok))`
/// - `Err(x)` to `Ok(Some(x))`
fn from_oak_status_result(
    result: Result<(), OakStatus>,
) -> Result<Option<wasmi::RuntimeValue>, wasmi::Trap> {
    let oak_status_from_result = result.map_or_else(|x: OakStatus| x, |()| OakStatus::Ok);
    let wasmi_value = wasmi::RuntimeValue::I32(oak_status_from_result as i32);
    Ok(Some(wasmi_value))
}
