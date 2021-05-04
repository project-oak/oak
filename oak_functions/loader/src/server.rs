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
use http::request::Request;
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Server,
};
use log::Level;
use oak_functions_abi::proto::{OakStatus, Response, StatusCode};
use prost::Message;
use serde::Deserialize;
use std::{convert::TryFrom, future::Future, net::SocketAddr, str, sync::Arc, time::Duration};
use wasmi::ValueType;

const MAIN_FUNCTION_NAME: &str = "main";
const ALLOC_FUNCTION_NAME: &str = "alloc";

/// Wasm host function index numbers for `wasmi` to map import names with. This numbering is not
/// exposed to the Wasm client. See https://docs.rs/wasmi/0.6.2/wasmi/trait.Externals.html
const READ_REQUEST: usize = 0;
const WRITE_RESPONSE: usize = 1;
const STORAGE_GET_ITEM: usize = 2;
const WRITE_LOG_MESSAGE: usize = 3;

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
/// the policy is violated.
const MIN_RESPONSE_SIZE: u32 = 50;

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
}

/// Creates an HTTP response, with status `OK`, and the protobuf-encoded `response` as its body.
///
/// To conform to the given security policy, the generated response is padded by adding a number of
/// unspecified characters, to make the total size of the response equal to
/// `policy.constant_response_size_bytes`. The padding is added as the value of the
/// `oak-policy-padding` header. If the size of the input `response`, encoded as a protobuf message,
/// is larger than `policy.constant_response_size_bytes` and the response is not already indicating
/// policy violation, then the `response` is discarded and an HTTP response indicating the policy
/// violation is returned. If `policy.constant_response_size_bytes` is too small even for the
/// policy-violation response, or the response already indicates a policy violation, this function
/// is recursively called to generate and return a response, where the protobuf-encoded body
/// encapsulates `StatusCode::PolicyViolationInError` and an empty inner body. The recursion is
/// guaranteed to terminate for a valid policy. If the policy is not valid, the function returns
/// early with an error.
fn create_response_and_apply_policy(
    response: Response,
    policy: &Policy,
) -> anyhow::Result<http::response::Response<Body>> {
    // check that the policy is valid
    policy.validate()?;

    // Serialize the response and get its size.
    let mut encoded = vec![];
    response
        .encode(&mut encoded)
        .context("couldn't encode response")?;
    let padding_length = i128::from(policy.constant_response_size_bytes)
        - i128::try_from(encoded.len()).context(format!(
            "cannot convert usize value {} to i128",
            encoded.len()
        ))?;

    if padding_length < 0 {
        let rsp = match StatusCode::from_i32(response.status) {
            // This match arm is not reachable, but is included to guarantee returning a
            // policy-conforming response, in case of a potential future breaking change.
            None => Response {
                status: StatusCode::InternalServerError as i32,
                body: "Reason: Invalid status code".as_bytes().to_vec(),
            },
            // If the `PolicySizeViolation` response itself is too large, return an error response
            // with the inner status code `PolicyViolationInError`. No more recursive calls will
            // happen after this point, since the size of the protobuf-encoded body is minimal in
            // this case, and is guaranteed to fit within the size specified by any valid policy.
            Some(StatusCode::PolicySizeViolation) => Response {
                status: StatusCode::PolicyViolationInError as i32,
                body: vec![],
            },
            // For all other status codes, return a `PolicySizeViolation`. Note that this may result
            // in one more recursive call, if the size of the response generated here is too large.
            _ => Response {
                status: StatusCode::PolicySizeViolation as i32,
                body: "Reason: the response is too large".as_bytes().to_vec(),
            },
        };
        // The match arms above guarantee that a termination condition will be met after a finite
        // number of recursive calls.
        create_response_and_apply_policy(rsp, policy)
    } else {
        let padding_length = usize::try_from(padding_length).context(format!(
            "cannot convert non-negative i128 value {} to usize",
            padding_length
        ))?;
        let padding_bytes = vec![b'x'; padding_length];

        // If `padding_length` is zero, the `oak-policy-padding` header is still added, but with
        // an empty string as the header value. The final encoding of the header in this case is
        // `oak-policy-padding: ` including the whitespace at the end. This guarantees that the
        // total size of the transmitted response remains constant.
        http::response::Builder::new()
            .status(hyper::StatusCode::OK)
            .header(POLICY_PADDING_HEADER, std::str::from_utf8(&padding_bytes)?)
            .body(Body::from(encoded))
            .context("couldn't create response")
    }
}

/// Creates an HTTP response, with status `OK` and the given `response` as the response body.
///
/// Encodes the given `response` as binary protobuf, and sets that as the body of the response.
/// This function is used when no security policy is provided.
fn create_http_response(rsp: Response) -> anyhow::Result<http::response::Response<Body>> {
    let mut encoded = vec![];
    rsp.encode(&mut encoded)
        .context("couldn't encode the response")?;
    http::response::Response::builder()
        .status(hyper::StatusCode::OK)
        .body(Body::from(encoded))
        .context("couldn't create the response")
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

    /// Corresponds to the host ABI function [`write_log_message`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#write_log_message).
    pub fn write_log_message(
        &mut self,
        buf_ptr: AbiPointer,
        buf_len: AbiPointerOffset,
    ) -> Result<(), OakStatus> {
        let raw_log = self
            .get_memory()
            .get(buf_ptr, buf_len as usize)
            .map_err(|err| {
                self.logger.log_sensitive(
                    Level::Error,
                    &format!(
                        "write_log_message(): Unable to read message from guest memory: {:?}",
                        err
                    ),
                );
                OakStatus::ErrInvalidArgs
            })?;
        let log_message = str::from_utf8(raw_log.as_slice()).map_err(|err| {
            self.logger.log_sensitive(
                Level::Warn,
                &format!(
                    "write_log_message(): Not a valid UTF-8 encoded string: {:?}\nContent: {:?}",
                    err, raw_log
                ),
            );
            OakStatus::ErrInvalidArgs
        })?;
        self.logger.log_sensitive(Level::Debug, log_message);
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
            WRITE_LOG_MESSAGE => {
                map_host_errors(self.write_log_message(args.nth_checked(0)?, args.nth_checked(1)?))
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
async fn apply_policy<F, S>(
    policy: Option<Policy>,
    function: F,
) -> anyhow::Result<http::response::Response<Body>>
where
    F: std::marker::Send + 'static + FnOnce() -> S,
    S: std::future::Future<Output = anyhow::Result<Response>> + std::marker::Send,
{
    match policy {
        None => create_http_response(function().await?),
        Some(policy) => {
            // Use tokio::spawn to actually run the tasks in parallel, for more accurate measurement
            // of time.
            let task = tokio::spawn(async move { function().await });
            // Sleep until the policy times out
            tokio::time::sleep(policy.constant_processing_time).await;

            let function_response = task.now_or_never();

            let response = match function_response {
                // The `function` did not terminate withing the policy timeout
                None => Response {
                    status: StatusCode::PolicyTimeViolation as i32,
                    body: "Reason: response not available".as_bytes().to_vec(),
                },
                Some(response) => match response {
                    // `tokio::task::JoinError` when getting the response from the tokio task
                    Err(_tokio_err) => Response {
                        status: StatusCode::InternalServerError as i32,
                        body: "Reason: internal server error".as_bytes().to_vec(),
                    },
                    Ok(response) => match response {
                        // The `function` terminated with an error
                        Err(err) => Response {
                            status: StatusCode::InternalServerError as i32,
                            body: err.to_string().as_bytes().to_vec(),
                        },
                        Ok(rsp) => rsp,
                    },
                },
            };
            create_response_and_apply_policy(response, &policy)
        }
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

    pub async fn handle_request(self, req: Request<Body>) -> anyhow::Result<Response> {
        self.logger
            .log_sensitive(Level::Info, &format!("The request is: {:?}", req));
        match (req.method(), req.uri().path()) {
            (&hyper::Method::POST, "/invoke") => self.handle_invoke(req).await,
            (method, path) => Ok(Response {
                status: StatusCode::BadRequest as i32,
                body: format!("Invalid request: {} {}\n", method, path)
                    .as_bytes()
                    .to_vec(),
            }),
        }
    }

    async fn handle_invoke(&self, req: Request<Body>) -> anyhow::Result<Response> {
        let request_bytes = hyper::body::to_bytes(req.into_body()).await.unwrap();
        let mut wasm_state = WasmState::new(
            &self.module,
            request_bytes.to_vec(),
            self.lookup_data.clone(),
            self.logger.clone(),
        )?;
        wasm_state.invoke();
        Ok(Response {
            status: StatusCode::Success as i32,
            body: wasm_state.get_response_bytes(),
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
        .http2_only(true)
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
        "write_log_message" => (
            WRITE_LOG_MESSAGE,
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
