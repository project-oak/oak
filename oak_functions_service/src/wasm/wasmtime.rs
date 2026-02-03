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

//! Wasm business logic provider based on [wasmtime](https://wasmtime.dev/).
//!
//! This file is mostly a copy of the file `mod.rs`, replacing `wasmi` with
//! `wasmtime`, and fixing some minor issues. The API of `wasmi` and `wasmtime`
//! are remarkably similar, so the changes are minimal.

extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

use alloc::{boxed::Box, format, rc::Rc, string::ToString, sync::Arc, vec::Vec};
use core::cell::Cell;
#[cfg(feature = "std")]
use std::time::Instant;

use log::Level;
use micro_rpc::StatusCode;
use oak_functions_abi::{Request, Response};
use oak_proto_rust::oak::functions::config::WasmtimeConfig;
use wasmtime::{PoolingAllocationConfig, Store};

use crate::{
    Handler, Observer,
    logger::{OakLogger, StandaloneLogger},
    lookup::LookupDataManager,
    wasm::{WasmApiFactory, api::StdWasmApiFactory},
};

/// Fixed name of the function to start a Wasm. Every Oak Wasm module must
/// provide this function.
pub const MAIN_FUNCTION_NAME: &str = "main";
/// Fixed name of the function to allocate memory. Every Oak Wasm module must
/// provide this function.
pub const ALLOC_FUNCTION_NAME: &str = "alloc";
/// The name of the memory every Oak Wasm module has.
pub const MEMORY_NAME: &str = "memory";

// Needs to be consistent with the definition of the Wasm import module in the
// Oak Functions ABI.
const OAK_FUNCTIONS: &str = "oak_functions";

/// Type aliases for positions in Wasm linear memory. Any future 64-bit version
/// of Wasm would use different types.
pub type AbiPointer = u32;
/// Type aliases for offsets in Wasm linear memory.
pub type AbiPointerOffset = u32;

/// `UserState` holds the user request bytes and response bytes for a particular
/// execution of an Oak Wasm module. The `UserState` also holds a reference to
/// the logger and the enabled extensions.
pub struct UserState {
    wasm_api_transport: Box<dyn micro_rpc::Transport<Error = !>>,
    logger: Arc<dyn OakLogger>,
}

/// Stubs a Wasm imported function in the provided linker.
///
/// The stubbed function logs an error and returns an error in the form of a
/// Wasm trap (similar to an exception).
macro_rules! stub_wasm_function {
    ($linker:ident, $function_mod:ident . $function_name:ident, ($($t:ty),*) -> $r:ty) => {
        $linker.func_wrap(
            stringify!($function_mod),
            stringify!($function_name),
            #[allow(unused_variables)]
            |caller: wasmtime::Caller<'_, UserState>, $(_: $t),*| {
                #[cfg(not(feature = "deny_sensitive_logging"))]
                caller
                    .data()
                    .log_error(concat!("called stubbed ", stringify!($function_mod), ".", stringify!($function_name)));
                Err::<$r, ::anyhow::Error>(
                    ::anyhow::anyhow!(
                        concat!("called stubbed ", stringify!($function_mod), ".", stringify!($function_name))))
            },
        )
        .expect(concat!("failed to define ", stringify!($function_mod), ".", stringify!($function_name), " in linker"));
    };
}

impl UserState {
    /// Stores the user request bytes, extensions, and logger. The response
    /// bytes are initialized with the empty response because every request
    /// needs to have a response and we fixed the empty response as the
    /// default response.
    fn new(
        wasm_api_transport: Box<dyn micro_rpc::Transport<Error = !>>,
        logger: Arc<dyn OakLogger>,
    ) -> Self {
        UserState { wasm_api_transport, logger }
    }

    // Use an `OakLogger` to log.
    fn log_error(&self, message: &str) {
        self.logger.log_sensitive(Level::Error, message)
    }
}

/// Exports the functions from the ABI of Oak Functions. These functions allow
/// the Wasm module to exchange data with Oak Functions and need the Wasm module
/// (or, more specifically, the [`OakCaller`]) to provide `alloc` for allocating
/// memory. The [`OakLinker`] checks that the Wasm module provides `alloc` and
/// `main`, which every Oak Wasm module must provide, and defines the memory
/// which the [`OakCaller`] uses.
struct OakLinker {
    linker: wasmtime::Linker<UserState>,
}

impl OakLinker {
    fn new(engine: &wasmtime::Engine) -> Self {
        let mut linker: wasmtime::Linker<UserState> = wasmtime::Linker::new(engine);

        linker
            .func_wrap(
                OAK_FUNCTIONS,
                // Corresponds to the OAK_FUNCTIONS ABI function [`invoke`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#invoke).
                "invoke",
                // The types in the signatures correspond to the parameters from
                // oak_functions_abi/src/lib.rs.
                |caller: wasmtime::Caller<'_, UserState>,
                 request_ptr: AbiPointer,
                 request_len: AbiPointerOffset,
                 response_ptr_ptr: AbiPointer,
                 response_len_ptr: AbiPointer| {
                    let mut caller = match OakCaller::new(caller) {
                        Ok(caller) => caller,
                        Err(oak_status) => return Ok(oak_status as i32),
                    };

                    let status = caller
                        .read_buffer(request_ptr, request_len)
                        .map_err(|err| {
                            caller.caller.data().log_error(&format!(
                                "Unable to read input from guest memory: {:?}",
                                err
                            ));
                            err
                        })
                        .and_then(|request| {
                            let user_state = caller.data_mut();
                            let response = user_state.wasm_api_transport.invoke(&request).into_ok();
                            caller.alloc_and_write(response_ptr_ptr, response_len_ptr, response)
                        });
                    from_status_code(status)
                },
            )
            .expect("failed to define invoke in linker");

        // TODO(#3929): One of our dependency requires various WASI functions to be
        // linked, but, to the best of our knowledge, does not use them at run
        // time. As a workaround, we stub them for now but we should remove
        // them, if possible.
        stub_wasm_function!(
            linker,
            wasi_snapshot_preview1.clock_time_get,
            (i32, i64, i32) -> i32
        );
        stub_wasm_function!(
            linker,
            wasi_snapshot_preview1.proc_exit,
            (i32) -> ()
        );
        stub_wasm_function!(
            linker,
            wasi_snapshot_preview1.environ_sizes_get,
            (i32, i32) -> i32
        );
        stub_wasm_function!(
            linker,
            wasi_snapshot_preview1.environ_get,
            (i32, i32) -> i32
        );
        stub_wasm_function!(
            linker,
            wasi_snapshot_preview1.fd_close,
            (i32) -> i32
        );
        stub_wasm_function!(
            linker,
            wasi_snapshot_preview1.fd_write,
            (i32, i32, i32, i32) -> i32
        );
        stub_wasm_function!(
            linker,
            wasi_snapshot_preview1.fd_read,
            (i32, i32, i32, i32) -> i32
        );
        stub_wasm_function!(
            linker,
            wasi_snapshot_preview1.fd_seek,
            (i32, i64, i32, i32) -> i32
        );

        OakLinker { linker }
    }

    /// Instantiates the Oak Linker and checks whether the instance exports
    /// `main`, `alloc` and a memory is attached.
    fn instantiate(
        &self,
        mut store: &mut Store<UserState>,
        module: &wasmtime::Module,
    ) -> Result<wasmtime::Instance, micro_rpc::Status> {
        let instance = self.linker.instantiate(&mut store, module).map_err(|err| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::Internal,
                format!("could not instantiate Wasm module: {:?}", err),
            )
        })?;
        // Use `main` as entry point.
        // .ensure_no_start(&mut store)
        // .map_err(|err| {
        //     micro_rpc::Status::new_with_message(
        //         micro_rpc::StatusCode::Internal,
        //         format!("failed to ensure no start in Wasm module: {:?}", err),
        //     )
        // })?;

        // Check that the instance exports "main".
        let _ =
            &instance.get_typed_func::<(), ()>(&mut store, MAIN_FUNCTION_NAME).map_err(|err| {
                micro_rpc::Status::new_with_message(
                    micro_rpc::StatusCode::Internal,
                    format!("couldn't validate `main` export: {:?}", err),
                )
            })?;

        // Check that the instance exports "alloc".
        let _ = &instance
            .get_typed_func::<i32, AbiPointer>(&mut store, ALLOC_FUNCTION_NAME)
            .map_err(|err| {
                micro_rpc::Status::new_with_message(
                    micro_rpc::StatusCode::Internal,
                    format!("couldn't validate `alloc` export: {:?}", err),
                )
            })?;

        // Make sure that non-empty `memory` is attached to the instance. Fail early if
        // `memory` is not available.
        instance.get_memory(store, MEMORY_NAME).ok_or_else(|| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::Internal,
                "couldn't find Wasm `memory` export".to_string(),
            )
        })?;

        Ok(instance)
    }
}

/// Provides functionality for reading from the Wasm memory, as well as
/// allocating and writing to the Wasm memory. The Wasm memory is defined by the
/// [`OakLinker`]. [`OakCaller`] relies on `alloc`, which every Oak Wasm module
/// must provide.
struct OakCaller<'a> {
    caller: wasmtime::Caller<'a, UserState>,
    alloc: wasmtime::TypedFunc<i32, AbiPointer>,
    memory: wasmtime::Memory,
}

impl<'a> OakCaller<'a> {
    fn new(mut caller: wasmtime::Caller<'a, UserState>) -> Result<Self, StatusCode> {
        // Get typed `alloc` to store.
        let ext = caller.get_export(ALLOC_FUNCTION_NAME).ok_or_else(|| {
            caller.data().log_error(&format!("failed to get exported {}", ALLOC_FUNCTION_NAME));
            StatusCode::Internal
        })?;

        let alloc = ext.into_func().ok_or_else(|| {
            caller.data().log_error(&format!("exported {} is not a func", ALLOC_FUNCTION_NAME));
            StatusCode::Internal
        })?;

        let typed_alloc = alloc.typed(&caller).ok().ok_or_else(|| {
            caller
                .data()
                .log_error(&format!("exported {} could not be typed", ALLOC_FUNCTION_NAME));
            StatusCode::Internal
        })?;

        // Get memory to store.
        let ext = caller.get_export(MEMORY_NAME).ok_or_else(|| {
            caller.data().log_error(&format!("failed to get exported {}", MEMORY_NAME));
            StatusCode::Internal
        })?;

        let memory = ext.into_memory().ok_or_else(|| {
            caller.data().log_error(&format!("exported {} is not a memory", MEMORY_NAME));
            StatusCode::Internal
        })?;

        let caller = OakCaller { caller, alloc: typed_alloc, memory };

        Ok(caller)
    }

    /// Reads the buffer starting at address `buf_ptr` with length `buf_len`
    /// from the Wasm memory.
    fn read_buffer(
        &self,
        buf_ptr: AbiPointer,
        buf_len: AbiPointerOffset,
    ) -> Result<Vec<u8>, StatusCode> {
        let mut buf = alloc::vec![0; buf_len as usize];
        let buf_ptr = buf_ptr
            .try_into()
            .expect("failed to convert AbiPointer to usize as required by wasmtime API");
        self.memory.read(&self.caller, buf_ptr, &mut buf).map_err(|err| {
            self.data().log_error(&format!("Unable to read buffer from guest memory: {:?}", err));
            StatusCode::InvalidArgument
        })?;
        Ok(buf)
    }

    /// Writes the given `buffer` by allocating `buffer.len()` Wasm memory and
    /// writing the address of the allocated memory to `dest_ptr_ptr` and
    /// the length to `dest_len_ptr`.
    fn alloc_and_write(
        &mut self,
        buf_ptr_ptr: AbiPointer,
        buf_ptr_len: AbiPointer,
        buf: Vec<u8>,
    ) -> Result<(), StatusCode> {
        let len = buf.len() as i32;

        // Allocate the memory from the Wasm module.
        // `address` will hold the address where memory of size len was allocated.
        let dest_ptr = self.alloc.call(&mut self.caller, len).expect("`alloc` call failed");

        // Write to the allocated memory.
        self.write_buffer(&buf, dest_ptr)?;
        self.write_u32(dest_ptr, buf_ptr_ptr)?;
        self.write_u32(len as u32, buf_ptr_len)?;
        Ok(())
    }

    /// Helper function to write the buffer `source` at the address `dest` of
    /// the Wasm memory, if `source` fits in the allocated memory.
    pub fn write_buffer(&mut self, source: &[u8], dest: AbiPointer) -> Result<(), StatusCode> {
        let dest = dest
            .try_into()
            .expect("failed to convert AbiPointer to usize as required by wasmtime API");
        self.memory.write(&mut self.caller, dest, source).map_err(|err| {
            self.data().log_error(&format!("Unable to write buffer into guest memory: {:?}", err));
            StatusCode::InvalidArgument
        })
    }

    /// Helper function to write the u32 `value` at the `address` of the Wasm
    /// memory.
    fn write_u32(&mut self, value: u32, address: AbiPointer) -> Result<(), StatusCode> {
        let value_bytes = value.to_le_bytes();
        self.write_buffer(&value_bytes, address).map_err(|err| {
            self.data()
                .log_error(&format!("Unable to write u32 value into guest memory: {:?}", err));
            StatusCode::InvalidArgument
        })
    }

    fn data_mut(&mut self) -> &mut UserState {
        self.caller.data_mut()
    }

    fn data(&self) -> &UserState {
        self.caller.data()
    }
}

// A request handler with a Wasm module for handling multiple requests.
pub struct WasmtimeHandler {
    wasm_module: wasmtime::Module,
    linker: OakLinker,
    wasm_api_factory: Box<dyn WasmApiFactory + Send + Sync>,
    logger: Arc<dyn OakLogger>,
    #[cfg_attr(not(feature = "std"), allow(dead_code))]
    observer: Option<Arc<dyn Observer + Send + Sync>>,
}

macro_rules! maybe_set {
    ($target:ident, $source:ident, [$( $field:ident $(as $ty:ty)?),+ ]) => {
        $(
            if let Some($field) = $source.$field {
                $target.$field($field $(as $ty)?);
            }
        )*
    };
}

impl WasmtimeHandler {
    pub fn create(
        wasm_module_bytes: &[u8],
        config_proto: WasmtimeConfig,
        wasm_api_factory: Box<dyn WasmApiFactory + Send + Sync>,
        logger: Box<dyn OakLogger>,
        observer: Option<Arc<dyn Observer + Send + Sync>>,
    ) -> anyhow::Result<Self> {
        let mut config = wasmtime::Config::new();
        config.cranelift_opt_level(wasmtime::OptLevel::Speed);

        if let Some(pooling_config_proto) = config_proto.pooling_strategy {
            let mut pooling_config = PoolingAllocationConfig::default();
            maybe_set!(
                pooling_config,
                pooling_config_proto,
                [
                    max_unused_warm_slots,
                    linear_memory_keep_resident as usize,
                    table_keep_resident as usize,
                    total_component_instances,
                    max_component_instance_size as usize,
                    max_core_instances_per_component,
                    max_memories_per_component,
                    max_tables_per_component,
                    total_memories,
                    total_tables,
                    total_stacks,
                    total_core_instances,
                    max_core_instance_size as usize,
                    max_tables_per_module,
                    table_elements,
                    max_memories_per_module
                ]
            );
            config
                .allocation_strategy(wasmtime::InstanceAllocationStrategy::Pooling(pooling_config));
        }
        maybe_set!(
            config,
            config_proto,
            [
                static_memory_maximum_size,
                static_memory_guard_size,
                dynamic_memory_guard_size,
                dynamic_memory_reserved_for_growth,
                memory_init_cow
            ]
        );

        let engine = wasmtime::Engine::new(&config)
            .map_err(|err| anyhow::anyhow!("couldn't create Wasmtime engine: {:?}", err))?;
        let wasm_module = wasmtime::Module::new(&engine, wasm_module_bytes)
            .map_err(|err| anyhow::anyhow!("couldn't load module from buffer: {:?}", err))?;

        let linker = OakLinker::new(wasm_module.engine());

        Ok(WasmtimeHandler {
            wasm_module,
            linker,
            wasm_api_factory,
            logger: Arc::from(logger),
            observer,
        })
    }
}

impl Handler for WasmtimeHandler {
    type HandlerType = WasmtimeHandler;
    type HandlerConfig = WasmtimeConfig;

    fn new_handler<const S: usize>(
        config: WasmtimeConfig,
        wasm_module_bytes: &[u8],
        lookup_data_manager: Arc<LookupDataManager<S>>,
        observer: Option<Arc<dyn Observer + Send + Sync>>,
    ) -> anyhow::Result<WasmtimeHandler> {
        let logger = Box::new(StandaloneLogger);
        let wasm_api_factory = Box::new(StdWasmApiFactory { lookup_data_manager });

        Self::create(wasm_module_bytes, config, wasm_api_factory, logger, observer)
    }

    fn handle_invoke(&self, invoke_request: Request) -> Result<Response, micro_rpc::Status> {
        #[cfg(feature = "std")]
        let now = Instant::now();

        let request = invoke_request.body;
        let response = Rc::new(Cell::new(Vec::new()));
        {
            let mut wasm_api = self.wasm_api_factory.create_wasm_api(request, response.clone());
            let user_state = UserState::new(wasm_api.transport(), self.logger.clone());
            // For isolated requests we need to create a new store for every request.
            let mut store = wasmtime::Store::new(self.wasm_module.engine(), user_state);
            let instance = self.linker.instantiate(&mut store, &self.wasm_module)?;

            // Does not work in wasmtime
            // #[cfg(not(feature = "deny_sensitive_logging"))]
            // instance.exports(&store).for_each(|export| {
            //     self.logger.log_sensitive(Level::Info, &format!("instance exports: {:?}",
            // export)) });

            // Invokes the Wasm module by calling main.
            let main = instance
                .get_typed_func::<(), ()>(&mut store, MAIN_FUNCTION_NAME)
                .expect("couldn't get `main` export");

            #[cfg(feature = "std")]
            if let Some(ref observer) = self.observer {
                observer.wasm_initialization(now.elapsed());
            }

            // Warning: if we implement constant-time execution policies, this metric can
            // leak the real execution time, so be sure that any time padding is
            // included in the metric.
            #[cfg(feature = "std")]
            let now = Instant::now();
            #[allow(unused)]
            let result = main.call(&mut store, ());
            #[cfg(feature = "std")]
            if let Some(ref observer) = self.observer {
                observer.wasm_invocation(now.elapsed());
            }

            #[cfg(not(feature = "deny_sensitive_logging"))]
            self.logger.log_sensitive(
                Level::Info,
                &format!("running Wasm module completed with result: {:?}", result),
            );
        }

        let response_bytes =
            Rc::into_inner(response).expect("response should have no references").into_inner();
        #[cfg(not(feature = "deny_sensitive_logging"))]
        self.logger.log_sensitive(Level::Info, &format!("response bytes: {:?}", response_bytes));

        let invoke_response =
            Response::create(oak_functions_abi::StatusCode::Success, response_bytes);
        Ok(invoke_response)
    }
}

/// A helper function to move between our specific result type `Result<(),
/// StatusCode>` and the `wasmtime` specific result type `Result<i32,
/// wasmtime::Trap>`.
fn from_status_code(result: Result<(), StatusCode>) -> anyhow::Result<i32> {
    let status_code = result.err().unwrap_or(StatusCode::Ok);
    Ok(status_code as i32)
}
