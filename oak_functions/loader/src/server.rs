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
use futures::future::FutureExt;
use log::Level;
use oak_functions_abi::proto::{OakStatus, Request, Response, ServerPolicy, StatusCode};
use serde::Deserialize;
use std::{collections::HashMap, convert::TryInto, str, sync::Arc, time::Duration};
use tokio::sync::mpsc::{channel, Receiver, Sender};
use wasmi::ValueType;

const MAIN_FUNCTION_NAME: &str = "main";
const ALLOC_FUNCTION_NAME: &str = "alloc";

/// Wasm host function index numbers for `wasmi` to map import names with. This numbering is not
/// exposed to the Wasm client. See https://docs.rs/wasmi/0.6.2/wasmi/trait.Externals.html
const READ_REQUEST: usize = 0;
const WRITE_RESPONSE: usize = 1;
const WRITE_LOG_MESSAGE: usize = 3;
const EXTENSION_INDEX_OFFSET: usize = 10;

// Type alias for a message sent over a channel through the ABI.
pub type AbiMessage = Vec<u8>;

// Bound on the amount of [`AbiMessage`]s an [`Endpoint`] can hold on the sender and the
// receiver individually. We fixed 100 arbitrarily, and it is the same for every Endpoint. We expect
// AbiMessages to be processed fast and do not expect to exceed the bound.
const ABI_CHANNEL_BOUND: usize = 100;

// Type aliases for positions and offsets in Wasm linear memory. Any future 64-bit version
// of Wasm would use different types.
pub type AbiPointer = u32;
pub type AbiPointerOffset = u32;
/// Wasm type identifier for position/offset values in linear memory. Any future 64-bit version of
/// Wasm would use a different value.
pub const ABI_USIZE: ValueType = ValueType::I32;

/// Minimum size of constant response bytes. It is large enough to fit an error response, in case
/// the policy is violated.
const MIN_RESPONSE_SIZE: u32 = 50;

/// Similar to [`ServerPolicy`], but it is used for reading the policy provided in the config,
/// and is therefore not guaranteed to be valid.
#[derive(Deserialize, Debug, Clone, Copy)]
#[serde(deny_unknown_fields)]
pub struct Policy {
    /// See [`Policy::constant_response_size_bytes`]
    pub constant_response_size_bytes: u32,
    /// A fixed response time. See [`ServerPolicy::constant_processing_time_ms`].
    #[serde(with = "humantime_serde")]
    pub constant_processing_time: Duration,
}

impl Policy {
    pub fn validate(&self) -> anyhow::Result<ServerPolicy> {
        anyhow::ensure!(
            self.constant_response_size_bytes >= MIN_RESPONSE_SIZE,
            "Response size is too small",
        );

        Ok(ServerPolicy {
            constant_response_size_bytes: self.constant_response_size_bytes,
            constant_processing_time_ms: self
                .constant_processing_time
                .as_millis()
                .try_into()
                .context("could not convert milliseconds to u32")?,
        })
    }
}

/// Trait with a single function for padding the body of an object so that it could be serialized
/// into a byte array of a fixed size.
trait FixedSizeBodyPadder {
    /// Adds padding to the body of this instance to make the size of the body equal to `body_size`.
    fn pad(&self, body_size: usize) -> anyhow::Result<Self>
    where
        Self: std::marker::Sized;
}

impl FixedSizeBodyPadder for Response {
    /// Creates and returns a new [`Response`] instance with the same `status` and `body` as `self`,
    /// except that the `body` may be padded, by adding a number trailing 0s, to make its length
    /// equal to `body_size`. Sets the `length` of the new instance to the length of `self.body`.
    /// Returns an error if the length of the `body` is larger than `body_size`.
    fn pad(&self, body_size: usize) -> anyhow::Result<Self> {
        if self.body.len() <= body_size {
            let mut body = self.body.as_slice().to_vec();
            // Set the length to the actual length of the body before padding.
            let length = body.len() as u64;
            // Add trailing 0s
            body.resize(body_size, 0);
            Ok(Response {
                status: self.status,
                body,
                length,
            })
        } else {
            anyhow::bail!("response body is larger than the input body_size")
        }
    }
}

/// Trait for implementing extensions, to implement new native functionality.
pub trait OakApiNativeExtension {
    /// Similar to `invoke_index` in [`wasmi::Externals`], but may return a result to be
    /// written into the memory of the `WasmState`.
    fn invoke(
        &mut self,
        wasm_state: &mut WasmState,
        args: wasmi::RuntimeArgs,
    ) -> Result<Result<(), OakStatus>, wasmi::Trap>;

    /// Metadata about this Extension, including the exported host function name, and the function's
    /// signature.
    fn get_metadata(&self) -> (String, wasmi::Signature);

    /// Performs any cleanup or terminating behavior necessary before destroying the WasmState.
    fn terminate(&mut self) -> anyhow::Result<()>;
}
pub trait ExtensionFactory {
    fn create(&self) -> anyhow::Result<BoxedExtension>;
}

pub type BoxedExtension = Box<dyn OakApiNativeExtension + Send + Sync>;
pub type BoxedExtensionFactory = Box<dyn ExtensionFactory + Send + Sync>;

/// `WasmState` holds runtime values for a particular execution instance of Wasm, handling a
/// single user request. The methods here correspond to the ABI host functions that allow the Wasm
/// module to exchange the request and the response with the Oak functions server. These functions
/// translate values between Wasm linear memory and Rust types.
pub struct WasmState {
    request_bytes: Vec<u8>,
    response_bytes: Vec<u8>,
    instance: Option<wasmi::ModuleRef>,
    memory: Option<wasmi::MemoryRef>,
    logger: Logger,
    /// A mapping of internal host functions to the corresponding [`OakApiNativeExtension`].
    extensions_indices: Option<HashMap<usize, BoxedExtension>>,
    /// A mapping of host function names to metadata required for resolving the function.
    extensions_metadata: HashMap<String, (usize, wasmi::Signature)>,
}

impl WasmState {
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
        self.logger
            .log_sensitive(Level::Debug, &format!("[Wasm] {}", log_message));
        Ok(())
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
            _ => {
                let mut extensions_indices = self
                    .extensions_indices
                    .take()
                    .expect("no extensions_indices is set");
                let extension = match extensions_indices.get_mut(&index) {
                    Some(extension) => Box::new(extension),
                    None => panic!("Unimplemented function at {}", index),
                };
                let result = map_host_errors(extension.invoke(self, args)?);
                self.extensions_indices = Some(extensions_indices);
                result
            }
        }
    }
}

impl wasmi::ModuleImportResolver for WasmState {
    fn resolve_func(
        &self,
        field_name: &str,
        signature: &wasmi::Signature,
    ) -> Result<wasmi::FuncRef, wasmi::Error> {
        // First look for the function (i.e., `field_name`) in the statically registered functions.
        // If not found, then look for it among the extensions. If not found, return an error.
        let (index, expected_signature) = match oak_functions_resolve_func(field_name) {
            Some(sig) => sig,
            None => match self.extensions_metadata.get(field_name) {
                Some((ind, sig)) => (*ind, sig.clone()),
                None => {
                    return Err(wasmi::Error::Instantiation(format!(
                        "Export {} not found",
                        field_name
                    )))
                }
            },
        };

        if signature != &expected_signature {
            return Err(wasmi::Error::Instantiation(format!(
                "Export `{}` doesn't match expected signature; got: {:?}, expected: {:?}",
                field_name, signature, expected_signature
            )));
        }

        Ok(wasmi::FuncInstance::alloc_host(expected_signature, index))
    }
}

impl WasmState {
    fn new(
        module: &wasmi::Module,
        request_bytes: Vec<u8>,
        logger: Logger,
        extensions_indices: HashMap<usize, BoxedExtension>,
        extensions_metadata: HashMap<String, (usize, wasmi::Signature)>,
    ) -> anyhow::Result<WasmState> {
        let mut abi = WasmState {
            request_bytes,
            response_bytes: vec![],
            instance: None,
            memory: None,
            logger,
            extensions_indices: Some(extensions_indices),
            extensions_metadata,
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

/// Runs the given function and applies the given security policy to the execution of the function
/// and the response returned from it. Serializes and returns the response as a binary
/// protobuf-encoded byte array of a constant size.
///
/// If the execution of the `function` takes longer than allowed by the given security policy,
/// an error response with status `PolicyTimeViolation` is returned. If the size of the `body` in
/// the response returned by the `function` is larger than allowed by the security policy, the
/// response is discarded and a response with status `PolicySizeViolation` is returned instead.
/// In all cases, to keep the total size of the returned byte array constant, the `body` of the
/// response may be padded by a number of trailing 0s before encoding the response as a binary
/// protobuf message. In this case, the `length` in the response will contain the effective length
/// of the `body`. This response is guaranteed to comply with the policy's size restriction.
pub async fn apply_policy<F, S>(policy: ServerPolicy, function: F) -> anyhow::Result<Response>
where
    F: std::marker::Send + 'static + FnOnce() -> S,
    S: std::future::Future<Output = anyhow::Result<Response>> + std::marker::Send,
{
    // Use tokio::spawn to actually run the tasks in parallel, for more accurate measurement
    // of time.
    let task = tokio::spawn(async move { function().await });
    // Sleep until the policy times out
    tokio::time::sleep(Duration::from_millis(
        policy.constant_processing_time_ms.into(),
    ))
    .await;

    let function_response = task.now_or_never();

    let response = match function_response {
        // The `function` did not terminate within the policy timeout
        None => Response::create(
            StatusCode::PolicyTimeViolation,
            "Reason: response not available.".as_bytes().to_vec(),
        ),
        Some(response) => match response {
            // `tokio::task::JoinError` when getting the response from the tokio task
            Err(_tokio_err) => Response::create(
                StatusCode::InternalServerError,
                "Reason: internal server error.".as_bytes().to_vec(),
            ),
            Ok(response) => match response {
                // The `function` terminated with an error
                Err(err) => Response::create(
                    StatusCode::InternalServerError,
                    err.to_string().as_bytes().to_vec(),
                ),
                Ok(rsp) => rsp,
            },
        },
    };

    // Return an error response if the body of the response is larger than allowed by the policy.
    let response = if response.body.len() > policy.constant_response_size_bytes as usize {
        Response::create(
            StatusCode::PolicySizeViolation,
            "Reason: the response is too large.".as_bytes().to_vec(),
        )
    } else {
        response
    };
    response.pad(
        policy
            .constant_response_size_bytes
            .try_into()
            .context("could not convert u64 to usize")?,
    )
}

// An ephemeral request handler with a Wasm module for handling the requests.
#[derive(Clone)]
pub struct WasmHandler {
    // Wasm module to be served on each invocation. `Arc` is needed to make `WasmHandler`
    // cloneable.
    module: Arc<wasmi::Module>,
    extension_factories: Arc<Vec<BoxedExtensionFactory>>,
    logger: Logger,
}

impl WasmHandler {
    pub fn create(
        wasm_module_bytes: &[u8],
        extension_factories: Vec<BoxedExtensionFactory>,
        logger: Logger,
    ) -> anyhow::Result<Self> {
        let module = wasmi::Module::from_buffer(&wasm_module_bytes)
            .map_err(|err| anyhow::anyhow!("could not load module from buffer: {:?}", err))?;

        Ok(WasmHandler {
            module: Arc::new(module),
            extension_factories: Arc::new(extension_factories),
            logger,
        })
    }

    pub async fn handle_invoke(&self, request: Request) -> anyhow::Result<Response> {
        let mut extensions_indices = HashMap::new();
        let mut extensions_metadata = HashMap::new();

        for (ind, factory) in self.extension_factories.iter().enumerate() {
            let extension = factory.create()?;
            let (name, signature) = extension.get_metadata();
            extensions_indices.insert(ind + EXTENSION_INDEX_OFFSET, extension);
            extensions_metadata.insert(name, (ind + EXTENSION_INDEX_OFFSET, signature));
        }

        let request_bytes = request.body;
        let mut wasm_state = WasmState::new(
            &self.module,
            request_bytes,
            self.logger.clone(),
            extensions_indices,
            extensions_metadata,
        )?;
        wasm_state.invoke();
        for mut extension in wasm_state
            .extensions_indices
            .take()
            .expect("no extensions_indices is set in wasm_state")
            .into_values()
        {
            extension.terminate()?;
        }
        Ok(Response::create(
            StatusCode::Success,
            wasm_state.get_response_bytes(),
        ))
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
        _ => return None,
    };

    Some((index, expected_signature))
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

/// Converts a binary sequence to a string if it is a valid UTF-8 string, or formats it as a numeric
/// vector of bytes otherwise.
pub fn format_bytes(v: &[u8]) -> String {
    std::str::from_utf8(v)
        .map(|s| s.to_string())
        .unwrap_or_else(|_| format!("{:?}", v))
}

// The Endpoint of a birectional channel. Sender and Receiver are exposed.
pub struct Endpoint {
    pub sender: Sender<AbiMessage>,
    pub receiver: Receiver<AbiMessage>,
}

/// Create a channel with two symmetrial endpoints. The [`AbiMessage`] sent from one [`Endpoint`]
/// are received at the other [`Endpoint`] and vice versa by connecting two unidirectional
/// [tokio::mpsc channels](https://docs.rs/tokio/0.1.16/tokio/sync/mpsc/index.html).
///
/// In ASCII art:
/// ```ignore
///   sender ____  ____ sender
///              \/
/// receiver ____/\____ receiver
/// ```
pub fn channel_create() -> (Endpoint, Endpoint) {
    let (tx0, rx0) = channel::<AbiMessage>(ABI_CHANNEL_BOUND);
    let (tx1, rx1) = channel::<AbiMessage>(ABI_CHANNEL_BOUND);
    let endpoint0 = Endpoint {
        sender: tx0,
        receiver: rx1,
    };
    let endpoint1 = Endpoint {
        sender: tx1,
        receiver: rx0,
    };
    (endpoint0, endpoint1)
}
