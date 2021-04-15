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

use crate::logger::Logger;
use anyhow::Context;
use byteorder::{ByteOrder, LittleEndian};
use http::{request::Request, response::Response};
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Server, StatusCode,
};
use log::Level;
use oak_functions_abi::proto::OakStatus;
use std::{net::SocketAddr, sync::Arc};
use wasmi::ValueType;

const MAIN_FUNCTION_NAME: &str = "main";

/// Wasm host function index numbers for `wasmi` to map import names with. This numbering is not
/// exposed to the Wasm client. See https://docs.rs/wasmi/0.6.2/wasmi/trait.Externals.html
const READ_REQUEST: usize = 0;
const WRITE_RESPONSE: usize = 1;

// Type aliases for positions and offsets in Wasm linear memory. Any future 64-bit version
// of Wasm would use different types.
type AbiPointer = u32;
type AbiPointerOffset = u32;
/// Wasm type identifier for position/offset values in linear memory. Any future 64-bit version of
/// Wasm would use a different value.
const ABI_USIZE: ValueType = ValueType::I32;

/// `WasmInterface` holds runtime values for a particular execution instance of Wasm, handling a
/// single user request. The methods here correspond to the ABI host functions that allow the Wasm
/// module to exchange the request and the response with the Oak functions server. These functions
/// translate values between Wasm linear memory and Rust types.
struct WasmInterface {
    request_bytes: Vec<u8>,
    response_bytes: Vec<u8>,
    memory: Option<wasmi::MemoryRef>,
    logger: Logger,
}

impl WasmInterface {
    pub fn new(request_bytes: Vec<u8>, logger: Logger) -> WasmInterface {
        WasmInterface {
            request_bytes,
            response_bytes: vec![],
            memory: None,
            logger,
        }
    }

    /// Helper function to get memory.
    fn get_memory(&self) -> &wasmi::MemoryRef {
        self.memory
            .as_ref()
            .expect("WasmInterface memory not attached!?")
    }

    /// Validates whether a given address range falls within the currently allocated range of guest
    /// memory.
    fn validate_ptr(&self, addr: AbiPointer, offset: AbiPointerOffset) -> Result<(), OakStatus> {
        let byte_size: wasmi::memory_units::Bytes = self.get_memory().current_size().into();

        if byte_size < wasmi::memory_units::Bytes((addr as usize) + (offset as usize)) {
            return Err(OakStatus::ErrInvalidArgs);
        }

        Ok(())
    }

    /// Corresponds to the host ABI function [`read_request`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#read_request).
    pub fn read_request(
        &self,
        dest: AbiPointer,
        dest_capacity: AbiPointerOffset,
        actual_length_addr: AbiPointer,
    ) -> Result<(), OakStatus> {
        self.validate_ptr(dest, dest_capacity)?;

        let raw_writer = &mut [0; 4];
        LittleEndian::write_u32(raw_writer, self.request_bytes.len() as u32);
        self.get_memory()
            .set(actual_length_addr, raw_writer)
            .map_err(|err| {
                self.logger.log_sensitive(
                    Level::Error,
                    &format!(
                        "read_request(): Unable to write actual length into guest memory: {:?}",
                        err
                    ),
                );
                OakStatus::ErrInvalidArgs
            })?;

        if dest_capacity >= self.request_bytes.len() as u32 {
            self.get_memory().set(dest, &self.request_bytes).map_err(|err| {
                    self.logger.log_sensitive(
                        Level::Error,
                        &format!(
                            "read_request(): Unable to write destination buffer into guest memory: {:?}",
                            err
                        ),
                    );
                    OakStatus::ErrInvalidArgs
                })?;
        } else {
            return Err(OakStatus::ErrBufferTooSmall);
        }

        Ok(())
    }

    /// Corresponds to the host ABI function [`write_response`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#write_response).
    pub fn write_response(
        &mut self,
        source: AbiPointer,
        source_length: AbiPointerOffset,
    ) -> Result<(), OakStatus> {
        let response = self
            .get_memory()
            .get(source, source_length as usize)
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
}

impl wasmi::Externals for WasmInterface {
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
            READ_REQUEST => map_host_errors(self.read_request(
                args.nth_checked(0)?,
                args.nth_checked(1)?,
                args.nth_checked(2)?,
            )),
            WRITE_RESPONSE => {
                map_host_errors(self.write_response(args.nth_checked(0)?, args.nth_checked(1)?))
            }
            _ => panic!("Unimplemented function at {}", index),
        }
    }
}

impl wasmi::ModuleImportResolver for WasmInterface {
    fn resolve_func(
        &self,
        field_name: &str,
        signature: &wasmi::Signature,
    ) -> Result<wasmi::FuncRef, wasmi::Error> {
        oak_functions_resolve_func(field_name, signature)
    }
}
/// Encapsulates the state of a Wasm invocation for a single user request.
struct WasmState {
    instance: wasmi::ModuleRef,
    abi: WasmInterface,
    logger: Logger,
}

impl WasmState {
    fn new(
        module: &wasmi::Module,
        request_bytes: Vec<u8>,
        logger: Logger,
    ) -> anyhow::Result<WasmState> {
        let mut abi = WasmInterface::new(request_bytes, logger.clone());
        let instance = wasmi::ModuleInstance::new(
            module,
            &wasmi::ImportsBuilder::new().with_resolver("oak_functions", &abi),
        )
        .context("failed to instantiate Wasm module")?
        .assert_no_start();

        // Make sure that non-empty `memory` is attached to the WasmInterface. Fail early if
        // `memory` is not available.
        abi.memory = Some(
            instance
                .export_by_name("memory")
                .context("could not find Wasm `memory` export")?
                .as_memory()
                .cloned()
                .context("could not interpret Wasm `memory` export as memory")?,
        );

        Ok(WasmState {
            instance,
            abi,
            logger,
        })
    }

    fn invoke(&mut self) {
        let result = self
            .instance
            .invoke_export(MAIN_FUNCTION_NAME, &[], &mut self.abi);
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
        self.abi.response_bytes.clone()
    }
}

// An ephemeral request handler with a Wasm module for handling the requests.
#[derive(Clone)]
pub(crate) struct WasmHandler {
    // Wasm module to be served on each invocation. `Arc` is needed to make `WasmHandler`
    // cloneable.
    module: Arc<wasmi::Module>,
    logger: Logger,
}

impl WasmHandler {
    pub(crate) fn create(wasm_module_bytes: &[u8], logger: Logger) -> anyhow::Result<Self> {
        let module = wasmi::Module::from_buffer(&wasm_module_bytes)?;
        Ok(WasmHandler {
            module: Arc::new(module),
            logger,
        })
    }

    pub(crate) async fn handle_request(
        &self,
        req: Request<Body>,
    ) -> anyhow::Result<Response<Body>> {
        self.logger
            .log_sensitive(Level::Info, &format!("The request is: {:?}", req));
        match (req.method(), req.uri().path()) {
            (&hyper::Method::POST, "/invoke") => self.handle_invoke(req).await,
            (method, path) => http::response::Builder::new()
                .status(StatusCode::BAD_REQUEST)
                .body(format!("Invalid request: {} {}\n", method, path).into())
                .context("Couldn't create response"),
        }
    }

    async fn handle_invoke(&self, req: Request<Body>) -> anyhow::Result<Response<Body>> {
        let request_bytes = hyper::body::to_bytes(req.into_body()).await.unwrap();
        let mut wasm_state =
            WasmState::new(&self.module, request_bytes.to_vec(), self.logger.clone())?;
        wasm_state.invoke();
        http::response::Builder::new()
            .status(StatusCode::OK)
            .body(Body::from(wasm_state.get_response_bytes()))
            .context("Couldn't create response")
    }
}

/// Starts an HTTP server on the given address, serving the main function of the given Wasm module.
pub async fn create_and_start_server(
    address: &SocketAddr,
    wasm_module_bytes: &[u8],
    notify_receiver: tokio::sync::oneshot::Receiver<()>,
    logger: Logger,
) -> anyhow::Result<()> {
    let wasm_handler = WasmHandler::create(wasm_module_bytes, logger.clone())?;

    // A `Service` is needed for every connection. Here we create a service using
    // the`wasm_handler`.
    let service = make_service_fn(move |_conn| {
        let wasm_handler = wasm_handler.clone();
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req| {
                let wasm_handler = wasm_handler.clone();
                async move { wasm_handler.handle_request(req).await }
            }))
        }
    });

    let server = Server::bind(address).serve(service);

    let graceful_server = server.with_graceful_shutdown(async {
        // Treat notification failure the same as a notification.
        let _ = notify_receiver.await;
    });

    logger.log_public(
        Level::Info,
        &format!(
            "{:?}: Started HTTP server on {:?}",
            std::thread::current().id(),
            &address
        ),
    );

    // Run until asked to terminate...
    let result = graceful_server.await;

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
    let (index, sig) = match field_name {
        "read_request" => (
            READ_REQUEST,
            wasmi::Signature::new(
                &[
                    ABI_USIZE, // dest
                    ABI_USIZE, // dest_capacity
                    ABI_USIZE, // actual_length_addr (out)
                ][..],
                Some(ValueType::I32),
            ),
        ),
        "write_response" => (
            WRITE_RESPONSE,
            wasmi::Signature::new(
                &[
                    ABI_USIZE, // source
                    ABI_USIZE, // source_length
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

    if &sig != signature {
        return Err(wasmi::Error::Instantiation(format!(
            "Export `{}` doesn't match expected type {:?}",
            field_name, signature
        )));
    }

    Ok(wasmi::FuncInstance::alloc_host(sig, index))
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
