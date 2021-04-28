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
use byteorder::{ByteOrder, LittleEndian};
use futures::future::FutureExt;
use http::{request::Request, response::Response};
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Server, StatusCode,
};
use log::Level;
use oak_functions_abi::proto::OakStatus;
use serde::Deserialize;
use std::{
    cmp::Ordering, convert::TryFrom, future::Future, net::SocketAddr, sync::Arc, time::Duration,
};
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

/// Specific header used for padding the response to match the expected response bytes
const POLICY_PADDING_HEADER: &str = "oak-policy-padding";

/// Minimum size of constant response bytes. It is large enough to fit an error response, in case
/// the policy is failed.
const MIN_RESPONSE_SIZE: u32 = 90;

/// A policy describing limits on the size of the response and response processing time to avoid
/// side-channel leaks.
#[derive(Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
pub struct Policy {
    /// A fixed size for responses returned by the trusted runtime.
    ///
    /// If the response computed by the Wasm module is smaller than this amount, it is padded with
    /// additional data before encryption in order to make the payload size exactly this size. If
    /// the response is larger than this amount, the trusted runtime discards the response and
    /// instead sends a response of exactly this size to the client, containing an error message
    /// indicating the failure.
    pub constant_response_size_bytes: u32,
    /// A fixed response time.
    ///
    /// Similar to the previous one, but controls the amount of time the function is allowed to run
    /// for. If the function finishes before this time, the response is not sent back until the
    /// time is elapsed. If the function does not finish within this deadline, the trusted runtime
    /// sends a response to the client containing an error message indicating the failure. The size
    /// of this response is equal to the size specified by the previous parameter.
    #[serde(with = "humantime_serde")]
    pub constant_processing_time: Duration,
}

impl Policy {
    pub fn validate(&self) -> anyhow::Result<()> {
        anyhow::ensure!(
            self.constant_response_size_bytes >= MIN_RESPONSE_SIZE,
            "Response size is too small",
        );
        Ok(())
    }

    /// Creates a an HTTP `INTERNAL_SERVER_ERROR` response, indicating the violation of the policy
    /// or some other internal error. The actual reason for the error is included in the body of the
    /// response. Additional padding may be added to make the total size of the response match the
    /// `constant_response_size_bytes` in the policy.
    fn create_error_response(&self, reason: &str) -> anyhow::Result<Response<Body>> {
        // We include the `oak-policy-padding` in all responses. So first estimate the size of
        // the response including this header name. The diff between this size and
        // `self.constant_response_size_bytes` gives the required padding, that will be added as the
        // value of the header.
        let body = format!("Reason: {}\n", reason);
        let estimates_size = estimate_error_response_size(body.clone())?;
        let required_padding = self.constant_response_size_bytes as i64 - estimates_size;

        if required_padding < 0 {
            anyhow::bail!("constant_response_size_bytes specified by the policy is too small.")
        } else {
            let padding_bytes = vec![b'0'; required_padding as usize];
            http::response::Builder::new()
                .status(StatusCode::INTERNAL_SERVER_ERROR)
                .header(POLICY_PADDING_HEADER, std::str::from_utf8(&padding_bytes)?)
                .body(body.into())
                .context("couldn't create response")
        }
    }

    /// Pads the response by adding a number of unspecified characters, to make the total size of
    /// the response equal to `self.constant_response_size_bytes`
    ///
    /// The zeros are added as the header value for header `oak-policy-padding`.
    /// Returns an error if the size of the input `response` is larger than or equal to
    /// `self.constant_response_size_bytes`.
    fn pad_response(&self, response: FunctionsResponse) -> anyhow::Result<Response<Body>> {
        let response_size = estimate_size(&response)?;
        let required_padding = self.constant_response_size_bytes as i64 - response_size;
        if required_padding < 0 {
            panic!(
                "Something is very wrong. Only call `pad_response` with responses that require padding."
            )
        } else {
            let padding_bytes = vec![b'0'; required_padding as usize];
            http::response::Builder::new()
                .status(response.status_code)
                .header(POLICY_PADDING_HEADER, std::str::from_utf8(&padding_bytes)?)
                .body(response.body.map(Body::from).unwrap_or_else(Body::empty))
                .context("couldn't create response")
        }
    }
}

/// The response from invoking the Wasm module functionality.
pub struct FunctionsResponse {
    pub status_code: StatusCode,
    pub body: Option<Vec<u8>>,
}

impl TryFrom<FunctionsResponse> for Response<Body> {
    type Error = http::Error;

    fn try_from(rsp: FunctionsResponse) -> Result<Self, Self::Error> {
        Response::builder()
            .status(rsp.status_code)
            .body(rsp.body.map(Body::from).unwrap_or_else(Body::empty))
    }
}

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

/// Runs the given function and applies the given policy to the execution and result of the
/// function.
///
/// If the policy is `None`, this function just runs the given function and returns its result.
/// If a policy is present, the given function is run, but its generated response is only returned
/// if allowed by the policy. If the execution of the function takes longer than allowed by the
/// policy, or the resulting response is larger than allowed by the policy, an error response
/// generated by the policy is returned instead of the actual response.
async fn apply_policy<F, S>(policy: Option<Policy>, function: F) -> anyhow::Result<Response<Body>>
where
    F: std::marker::Send + 'static + FnOnce() -> S,
    S: std::future::Future<Output = anyhow::Result<FunctionsResponse>> + std::marker::Send,
{
    match policy {
        None => Response::<Body>::try_from(function().await?).context("couldn't get the response"),
        Some(policy) => {
            // Use tokio::spawn to actually run the tasks in parallel, for more accurate measurement
            // of time.
            let task = tokio::spawn(async move { function().await });
            tokio::time::sleep(policy.constant_processing_time).await;

            let response = task.now_or_never();

            match response {
                None => policy.create_error_response("response not available"),
                Some(response) => match response {
                    Err(err) => policy.create_error_response(format!("{}", err).as_str()),
                    Ok(response) => match response {
                        Err(err) => policy.create_error_response(format!("{}", err).as_str()),
                        Ok(rsp) => {
                            // All responses from Oak-Functions have an additional
                            // `oak-policy-padding` header.
                            let size = estimate_size(&rsp)?;
                            match size.cmp(&(policy.constant_response_size_bytes as i64)) {
                                Ordering::Greater => {
                                    policy.create_error_response("response too large")
                                }
                                Ordering::Less => policy.pad_response(rsp),
                                Ordering::Equal => Response::<Body>::try_from(rsp)
                                    .context("couldn't get the response"),
                            }
                        }
                    },
                },
            }
        }
    }
}

// TODO(#2032): Use custom body, to avoid the need for this estimation.
/// Estimates the size of the given response.
///
/// Measures the size of the response when formatted according to
/// [RFC-2616](https://tools.ietf.org/html/rfc2616#section-6).
/// The only relevant parts of the response are the status code and the response body. We also add
/// the `oak-policy-padding` header to all responses. This header name is therefore also included
/// when estimating the size.
/// The final response send to the client, will in addition contain `date` and `content-length`
/// headers. Those add constant size and are omitted from this calculation.
fn estimate_size(response: &FunctionsResponse) -> anyhow::Result<i64> {
    // Status-Line = HTTP-Version SP Status-Code SP Reason-Phrase CRLF
    let status_line = format!(
        "HTTP/1.1 {} {}\r\n",
        response.status_code.as_u16(),
        response.status_code.canonical_reason().unwrap()
    );

    // The header value will be the required padding. For the now, we leave it empty.
    let response_header = format!("{} : {}\r\n", POLICY_PADDING_HEADER, "");

    // Encoding the entire response including the body requires consuming the response. To avoid
    // that, we format the response without the body, then add the body size separately.
    let encoded_response = format!("{}{}\r\n", status_line, response_header);

    // Get body size
    let body_size = match &response.body {
        None => 0,
        Some(vec) => vec.len(),
    };

    Ok(encoded_response.len() as i64 + body_size as i64)
}

fn estimate_error_response_size(body: String) -> anyhow::Result<i64> {
    estimate_size(&FunctionsResponse {
        status_code: StatusCode::INTERNAL_SERVER_ERROR,
        body: Some(body.as_bytes().to_vec()),
    })
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

    pub async fn handle_request(self, req: Request<Body>) -> anyhow::Result<FunctionsResponse> {
        self.logger
            .log_sensitive(Level::Info, &format!("The request is: {:?}", req));
        match (req.method(), req.uri().path()) {
            (&hyper::Method::POST, "/invoke") => self.handle_invoke(req).await,
            (method, path) => Ok(FunctionsResponse {
                status_code: StatusCode::BAD_REQUEST,
                body: Some(
                    format!("Invalid request: {} {}\n", method, path)
                        .as_bytes()
                        .to_vec(),
                ),
            }),
        }
    }

    async fn handle_invoke(&self, req: Request<Body>) -> anyhow::Result<FunctionsResponse> {
        let request_bytes = hyper::body::to_bytes(req.into_body()).await.unwrap();
        let mut wasm_state = WasmState::new(
            &self.module,
            request_bytes.to_vec(),
            self.lookup_data.clone(),
            self.logger.clone(),
        )?;
        wasm_state.invoke();
        Ok(FunctionsResponse {
            status_code: StatusCode::OK,
            body: Some(wasm_state.get_response_bytes()),
        })
    }
}

/// Starts an HTTP server on the given address, serving the main function of the given Wasm module.
pub async fn create_and_start_server<F: Future<Output = ()>>(
    address: &SocketAddr,
    wasm_module_bytes: &[u8],
    lookup_data: Arc<LookupData>,
    policy: Option<Policy>,
    terminate: F,
    logger: Logger,
) -> anyhow::Result<()> {
    let wasm_handler = WasmHandler::create(wasm_module_bytes, lookup_data, logger.clone())?;

    // A `Service` is needed for every connection. Here we create a service using the
    // `wasm_handler`.
    let service = make_service_fn(move |_conn| {
        let wasm_handler = wasm_handler.clone();
        let policy = policy.clone();
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req| {
                let wasm_handler = wasm_handler.clone();
                let policy = policy.clone();
                let func = move || wasm_handler.handle_request(req);
                async move { apply_policy(policy, func).await }
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
