//
// Copyright 2021 The Project Oak Authors
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

use crate::{logger::Logger, lookup::LookupData};
use anyhow::Context;
use async_stream::stream;
use byteorder::{ByteOrder, LittleEndian};
use http::{request::Request, response::Response};
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Server, StatusCode,
};
use log::Level;
use oak_functions_abi::proto::OakStatus;
use std::{future::Future, net::SocketAddr, sync::Arc};
use tokio_stream::StreamExt;
use wasmi::ValueType;

const MAIN_FUNCTION_NAME: &str = "main";
const ALLOC_FUNCTION_NAME: &str = "alloc";

/// Wasm host function index numbers for `wasmi` to map import names with. This numbering is not
/// exposed to the Wasm client. See https://docs.rs/wasmi/0.6.2/wasmi/trait.Externals.html
const READ_REQUEST: usize = 0;
const WRITE_RESPONSE: usize = 1;
const STORAGE_GET_ITEM: usize = 2;

// Type aliases for positions and offsets in Wasm linear memory. Any future 64-bit version
// of Wasm would use different types.
type AbiPointer = u32;
type AbiPointerOffset = u32;
/// Wasm type identifier for position/offset values in linear memory. Any future 64-bit version of
/// Wasm would use a different value.
const ABI_USIZE: ValueType = ValueType::I32;

/// `WasmState` holds runtime values for a particular execution instance of Wasm, handling a
/// single user request. The methods here correspond to the ABI host functions that allow the Wasm
/// module to exchange the request and the response with the Oak functions server. These functions
/// translate values between Wasm linear memory and Rust types.
struct WasmState {
    request_bytes: Vec<u8>,
    response_bytes: Vec<u8>,
    lookup_data: Arc<LookupData>,
    instance: Option<wasmi::ModuleRef>,
    memory: Option<wasmi::MemoryRef>,
    logger: Logger,
}

impl WasmState {
    /// Helper function to get memory.
    fn get_memory(&self) -> &wasmi::MemoryRef {
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

    fn write_buffer_to_wasm_memory(
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

    fn write_u32_to_wasm_memory(&self, value: u32, address: AbiPointer) -> Result<(), OakStatus> {
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

    /// Corresponds to the host ABI function [`storage_get_item`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#storage_get_item).
    pub fn storage_get_item(
        &mut self,
        key_ptr: AbiPointer,
        key_len: AbiPointerOffset,
        value_ptr_ptr: AbiPointer,
        value_len_ptr: AbiPointer,
    ) -> Result<(), OakStatus> {
        let key = self
            .get_memory()
            .get(key_ptr, key_len as usize)
            .map_err(|err| {
                self.logger.log_sensitive(
                    Level::Error,
                    &format!(
                        "storage_get_item(): Unable to read key from guest memory: {:?}",
                        err
                    ),
                );
                OakStatus::ErrInvalidArgs
            })?;
        self.logger.log_sensitive(
            Level::Debug,
            &format!("storage_get_item(): key: {:?}", std::str::from_utf8(&key)),
        );
        match self.lookup_data.get(&key) {
            Some(value) => {
                self.logger.log_sensitive(
                    Level::Debug,
                    &format!(
                        "storage_get_item(): value: {:?}",
                        std::str::from_utf8(&value)
                    ),
                );
                let dest_ptr = self.alloc(value.len() as u32);
                self.write_buffer_to_wasm_memory(&value, dest_ptr)?;
                self.write_u32_to_wasm_memory(dest_ptr, value_ptr_ptr)?;
                self.write_u32_to_wasm_memory(value.len() as u32, value_len_ptr)?;
                Ok(())
            }
            None => {
                self.logger
                    .log_sensitive(Level::Debug, "storage_get_item(): value not found");
                Err(OakStatus::ErrStorageItemNotFound)
            }
        }
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
}

impl wasmi::Externals for WasmState {
    /// Invocation of a host function specified by its registered index. Acts as a wrapper for
    /// the relevant native function, just:
    /// - checking argument types (which should be correct as `wasmi` will only pass through those
    ///   types that were specified when the host function was registered with `resolv_func`).
    /// - mapping resulting return/error values.
    fn invoke_index(
        &mut self,
        index: usize,
        args: wasmi::RuntimeArgs,
    ) -> Result<Option<wasmi::RuntimeValue>, wasmi::Trap> {
        match index {
            READ_REQUEST => {
                map_host_errors(self.read_request(args.nth_checked(0)?, args.nth_checked(1)?))
            }
            WRITE_RESPONSE => {
                map_host_errors(self.write_response(args.nth_checked(0)?, args.nth_checked(1)?))
            }
            STORAGE_GET_ITEM => map_host_errors(self.storage_get_item(
                args.nth_checked(0)?,
                args.nth_checked(1)?,
                args.nth_checked(2)?,
                args.nth_checked(3)?,
            )),
            _ => panic!("Unimplemented function at {}", index),
        }
    }
}

impl wasmi::ModuleImportResolver for WasmState {
    fn resolve_func(
        &self,
        field_name: &str,
        signature: &wasmi::Signature,
    ) -> Result<wasmi::FuncRef, wasmi::Error> {
        oak_functions_resolve_func(field_name, signature)
    }
}

impl WasmState {
    fn new(
        module: &wasmi::Module,
        request_bytes: Vec<u8>,
        lookup_data: Arc<LookupData>,
        logger: Logger,
    ) -> anyhow::Result<WasmState> {
        let mut abi = WasmState {
            request_bytes,
            response_bytes: vec![],
            lookup_data,
            instance: None,
            memory: None,
            logger,
        };

        let instance = wasmi::ModuleInstance::new(
            module,
            &wasmi::ImportsBuilder::new().with_resolver("oak_functions", &abi),
        )
        .context("failed to instantiate Wasm module")?
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
            &format!(
                "{:?}: Running Wasm module completed with result: {:?}",
                std::thread::current().id(),
                result
            ),
        );
    }

    fn get_response_bytes(&self) -> Vec<u8> {
        self.response_bytes.clone()
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
pub struct WasmHandler {
    // Wasm module to be served on each invocation. `Arc` is needed to make `WasmHandler`
    // cloneable.
    module: Arc<wasmi::Module>,
    lookup_data: Arc<LookupData>,
    logger: Logger,
}

fn t() -> impl futures_core::Stream<
    Item = Result<bytes::Bytes, Box<dyn std::error::Error + Send + Sync + 'static>>,
> {
    stream! {
        yield Ok::<_, Box<_>>(bytes::Bytes::from("Hello world"));
    }
}

fn u() -> impl futures_core::Stream<
    Item = Result<bytes::Bytes, Box<dyn std::error::Error + Send + Sync + 'static>>,
> {
    let (tx, rx) = tokio::sync::mpsc::channel(10);
    let s = tokio_stream::wrappers::ReceiverStream::new(rx);
    s
}

fn s(
    mut r: hyper::Body,
) -> Box<
    (dyn futures_core::Stream<
        Item = Result<bytes::Bytes, Box<dyn std::error::Error + Send + Sync + 'static>>,
    > + Send
         + 'static),
> {
    Box::new(stream! {
        let _m0 = r.next().await;
        yield Ok("Hello world".into());
        let _m1 = r.next().await;
        yield Ok("Hello world".into());
    })
}

impl WasmHandler {
    pub fn create(
        wasm_module_bytes: &[u8],
        lookup_data: Arc<LookupData>,
        logger: Logger,
    ) -> anyhow::Result<Self> {
        let module = wasmi::Module::from_buffer(&wasm_module_bytes)?;
        Ok(WasmHandler {
            module: Arc::new(module),
            lookup_data,
            logger,
        })
    }

    pub async fn handle_request(&self, req: Request<Body>) -> anyhow::Result<Response<Body>> {
        self.logger
            .log_sensitive(Level::Info, &format!("The request is: {:?}", req));
        match (req.method(), req.uri().path()) {
            (&hyper::Method::POST, "/invoke") => self.handle_invoke(req).await,
            (&hyper::Method::POST, "/test") => Ok(http::response::Builder::new()
                .body(s(req.into_body()).into())
                .unwrap()),
            (method, path) => http::response::Builder::new()
                .status(StatusCode::BAD_REQUEST)
                .body(format!("Invalid request: {} {}\n", method, path).into())
                .context("Couldn't create response"),
        }
    }

    async fn handle_invoke(&self, req: Request<Body>) -> anyhow::Result<Response<Body>> {
        let request_bytes = hyper::body::to_bytes(req.into_body()).await.unwrap();
        let mut wasm_state = WasmState::new(
            &self.module,
            request_bytes.to_vec(),
            self.lookup_data.clone(),
            self.logger.clone(),
        )?;
        wasm_state.invoke();
        http::response::Builder::new()
            .status(StatusCode::OK)
            .body(Body::from(wasm_state.get_response_bytes()))
            .context("Couldn't create response")
    }
}

/// Starts an HTTP server on the given address, serving the main function of the given Wasm module.
pub async fn create_and_start_server<F: Future<Output = ()>>(
    address: &SocketAddr,
    wasm_module_bytes: &[u8],
    lookup_data: Arc<LookupData>,
    terminate: F,
    logger: Logger,
) -> anyhow::Result<()> {
    let wasm_handler = WasmHandler::create(wasm_module_bytes, lookup_data, logger.clone())?;

    // A `Service` is needed for every connection. Here we create a service using the
    // `wasm_handler`.
    let service = make_service_fn(move |_conn| {
        let wasm_handler = wasm_handler.clone();
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req| {
                let wasm_handler = wasm_handler.clone();
                async move { wasm_handler.handle_request(req).await }
            }))
        }
    });

    let server = Server::bind(address)
        .serve(service)
        .with_graceful_shutdown(terminate);

    logger.log_public(
        Level::Info,
        &format!(
            "{:?}: Started HTTP server on {:?}",
            std::thread::current().id(),
            &address
        ),
    );

    // Run until asked to terminate...
    let result = server.await;

    logger.log_public(
        Level::Info,
        &format!(
            "HTTP server on addr {} terminated with {:?}",
            &address, result
        ),
    );
    Ok(())
}

/// A resolver function, mapping `oak_functions` host function names to an index and a type
/// signature.
fn oak_functions_resolve_func(
    field_name: &str,
    signature: &wasmi::Signature,
) -> Result<wasmi::FuncRef, wasmi::Error> {
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
        "storage_get_item" => (
            STORAGE_GET_ITEM,
            wasmi::Signature::new(
                &[
                    ABI_USIZE, // key_ptr
                    ABI_USIZE, // key_len
                    ABI_USIZE, // value_ptr_ptr
                    ABI_USIZE, // value_len_ptr
                ][..],
                Some(ValueType::I32),
            ),
        ),
        _ => {
            return Err(wasmi::Error::Instantiation(format!(
                "Export {} not found",
                field_name
            )))
        }
    };

    if signature != &expected_signature {
        return Err(wasmi::Error::Instantiation(format!(
            "Export `{}` doesn't match expected signature; got: {:?}, expected: {:?}",
            field_name, signature, expected_signature
        )));
    }

    Ok(wasmi::FuncInstance::alloc_host(expected_signature, index))
}

/// A helper function to move between our specific result type `Result<(), OakStatus>` and the
/// `wasmi` specific result type `Result<Option<wasmi::RuntimeValue>, wasmi::Trap>`, mapping:
/// - `Ok(())` to `Ok(Some(OakStatus::Ok))`
/// - `Err(x)` to `Ok(Some(x))`
fn map_host_errors(
    result: Result<(), OakStatus>,
) -> Result<Option<wasmi::RuntimeValue>, wasmi::Trap> {
    Ok(Some(wasmi::RuntimeValue::I32(result.map_or_else(
        |x: OakStatus| x as i32,
        |_| OakStatus::Ok as i32,
    ))))
}
