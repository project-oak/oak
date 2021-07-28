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

use crate::{logger::Logger, lookup::LookupData, tf::TensorFlowModel};
use anyhow::Context;
use byteorder::{ByteOrder, LittleEndian};
use futures::future::FutureExt;
use log::Level;
use oak_functions_abi::proto::{OakStatus, Request, Response, StatusCode};
use prost::Message;
use serde::Deserialize;
use std::{convert::TryFrom, str, sync::Arc, time::Duration};
use wasmi::ValueType;

const MAIN_FUNCTION_NAME: &str = "main";
const ALLOC_FUNCTION_NAME: &str = "alloc";

/// Wasm host function index numbers for `wasmi` to map import names with. This numbering is not
/// exposed to the Wasm client. See https://docs.rs/wasmi/0.6.2/wasmi/trait.Externals.html
const READ_REQUEST: usize = 0;
const WRITE_RESPONSE: usize = 1;
const STORAGE_GET_ITEM: usize = 2;
const WRITE_LOG_MESSAGE: usize = 3;
const TF_MODEL_GET_SHAPE: usize = 4;
const TF_MODEL_INFER: usize = 5;

// Type aliases for positions and offsets in Wasm linear memory. Any future 64-bit version
// of Wasm would use different types.
type AbiPointer = u32;
type AbiPointerOffset = u32;
/// Wasm type identifier for position/offset values in linear memory. Any future 64-bit version of
/// Wasm would use a different value.
const ABI_USIZE: ValueType = ValueType::I32;

/// Minimum size of constant response bytes. It is large enough to fit an error response, in case
/// the policy is violated.
const MIN_RESPONSE_SIZE: usize = 50;

/// A policy describing limits on the size of the response and response processing time to avoid
/// side-channel leaks.
#[derive(Deserialize, Debug, Clone, Copy)]
#[serde(deny_unknown_fields)]
pub struct Policy {
    /// A fixed size for responses returned by the trusted runtime.
    ///
    /// This size only applies to the body of the Oak Functions response. If the response body
    /// computed by the Wasm module is smaller than this amount, it is padded with additional
    /// data before serialization and inclusion in the HTTP response to the client. If the body is
    /// larger than this amount, the trusted runtime discards the response and instead uses a
    /// response with a body of exactly this size, containing an error message indicating the
    /// policy violation. The body included in the HTTP response sent to the client is the binary
    /// protobuf encoding of the Oak Functions response, and will have a size larger than
    /// `constant_response_size_bytes`. However, this size is still guaranteed to be a constant.
    pub constant_response_size_bytes: usize,
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

/// Similar to [`Policy`], but it is guaranteed to be valid. An instance of this can only be created
/// from a valid [`Policy`] by calling `try_into` on it.
pub struct ValidatedPolicy {
    /// See [`Policy::constant_response_size_bytes`]
    constant_response_size_bytes: usize,
    /// See [`Policy::constant_processing_time`]
    constant_processing_time: Duration,
}

impl TryFrom<Policy> for ValidatedPolicy {
    type Error = anyhow::Error;

    fn try_from(policy: Policy) -> anyhow::Result<Self> {
        policy.validate()?;
        Ok(ValidatedPolicy {
            constant_response_size_bytes: policy.constant_response_size_bytes,
            constant_processing_time: policy.constant_processing_time,
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

/// `WasmState` holds runtime values for a particular execution instance of Wasm, handling a
/// single user request. The methods here correspond to the ABI host functions that allow the Wasm
/// module to exchange the request and the response with the Oak functions server. These functions
/// translate values between Wasm linear memory and Rust types.
struct WasmState {
    request_bytes: Vec<u8>,
    response_bytes: Vec<u8>,
    lookup_data: Arc<LookupData>,
    tf_model: Arc<Option<TensorFlowModel>>,
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
        self.logger
            .log_sensitive(Level::Debug, &format!("[Wasm] {}", log_message));
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
            &format!("storage_get_item(): key: {}", format_bytes(&key)),
        );
        match self.lookup_data.get(&key) {
            Some(value) => {
                // Truncate value for logging.
                let value_to_log = value.clone().into_iter().take(512).collect::<Vec<_>>();
                self.logger.log_sensitive(
                    Level::Debug,
                    &format!("storage_get_item(): value: {}", format_bytes(&value_to_log)),
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

    /// Corresponds to the host ABI function [`tf_model_get_shape`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#tf_model_get_shape).
    pub fn tf_model_get_shape(
        &mut self,
        shape_ptr_ptr: AbiPointer,
        shape_len_ptr: AbiPointer,
    ) -> Result<(), OakStatus> {
        match *self.tf_model {
            None => Err(OakStatus::ErrTensorFlowModelNotFound),
            Some(ref tf_model) => {
                let shape = tf_model.shape.clone();
                let shape_ptr = self.alloc(shape.len() as u32);
                self.write_buffer_to_wasm_memory(&shape, shape_ptr)?;
                self.write_u32_to_wasm_memory(shape_ptr, shape_ptr_ptr)?;
                self.write_u32_to_wasm_memory(shape.len() as u32, shape_len_ptr)?;
                Ok(())
            }
        }
    }

    /// Corresponds to the host ABI function [`tf_model_infer`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#tf_model_infer).
    pub fn tf_model_infer(
        &mut self,
        input_ptr: AbiPointer,
        input_len: AbiPointerOffset,
        inference_ptr_ptr: AbiPointer,
        inference_len_ptr: AbiPointer,
    ) -> Result<(), OakStatus> {
        match *self.tf_model {
            None => Err(OakStatus::ErrTensorFlowModelNotFound),
            Some(ref tf_model) => {
                let input = self
                    .get_memory()
                    .get(input_ptr, input_len as usize)
                    .map_err(|err| {
                        self.logger.log_sensitive(
                            Level::Error,
                            &format!(
                                "tf_model_infer(): Unable to read input from guest memory: {:?}",
                                err
                            ),
                        );
                        OakStatus::ErrInvalidArgs
                    })?;

                let shape = tf_model
                    .shape
                    .clone()
                    .iter()
                    .cloned()
                    .map(|u| u.into())
                    .collect::<Vec<usize>>();

                // Get the inference, and convert it into a protobuf-encoded byte array
                let inference = tf_model.get_inference(&input, &shape);
                let mut encoded_inference = vec![];
                inference.encode(&mut encoded_inference).unwrap();

                let inference_ptr = self.alloc(encoded_inference.len() as u32);
                self.write_buffer_to_wasm_memory(&encoded_inference, inference_ptr)?;
                self.write_u32_to_wasm_memory(inference_ptr, inference_ptr_ptr)?;
                self.write_u32_to_wasm_memory(encoded_inference.len() as u32, inference_len_ptr)?;
                Ok(())
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
            TF_MODEL_GET_SHAPE => {
                map_host_errors(self.tf_model_get_shape(args.nth_checked(0)?, args.nth_checked(1)?))
            }
            TF_MODEL_INFER => map_host_errors(self.tf_model_infer(
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
        tf_model: Arc<Option<TensorFlowModel>>,
        logger: Logger,
    ) -> anyhow::Result<WasmState> {
        let mut abi = WasmState {
            request_bytes,
            response_bytes: vec![],
            lookup_data,
            tf_model,
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
pub async fn apply_policy<F, S>(policy: ValidatedPolicy, function: F) -> anyhow::Result<Response>
where
    F: std::marker::Send + 'static + FnOnce() -> S,
    S: std::future::Future<Output = anyhow::Result<Response>> + std::marker::Send,
{
    // Use tokio::spawn to actually run the tasks in parallel, for more accurate measurement
    // of time.
    let task = tokio::spawn(async move { function().await });
    // Sleep until the policy times out
    tokio::time::sleep(policy.constant_processing_time).await;

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
    let response = if response.body.len() > policy.constant_response_size_bytes {
        Response::create(
            StatusCode::PolicySizeViolation,
            "Reason: the response is too large.".as_bytes().to_vec(),
        )
    } else {
        response
    };
    response.pad(policy.constant_response_size_bytes)
}

// An ephemeral request handler with a Wasm module for handling the requests.
#[derive(Clone)]
pub struct WasmHandler {
    // Wasm module to be served on each invocation. `Arc` is needed to make `WasmHandler`
    // cloneable.
    module: Arc<wasmi::Module>,
    lookup_data: Arc<LookupData>,
    tf_model: Arc<Option<TensorFlowModel>>,
    logger: Logger,
}

impl WasmHandler {
    pub fn create(
        wasm_module_bytes: &[u8],
        lookup_data: Arc<LookupData>,
        tf_model: Arc<Option<TensorFlowModel>>,
        logger: Logger,
    ) -> anyhow::Result<Self> {
        let module = wasmi::Module::from_buffer(&wasm_module_bytes)?;
        Ok(WasmHandler {
            module: Arc::new(module),
            lookup_data,
            tf_model,
            logger,
        })
    }

    pub async fn handle_invoke(&self, request: Request) -> anyhow::Result<Response> {
        let request_bytes = request.body;
        let mut wasm_state = WasmState::new(
            &self.module,
            request_bytes,
            self.lookup_data.clone(),
            self.tf_model.clone(),
            self.logger.clone(),
        )?;
        wasm_state.invoke();
        Ok(Response::create(
            StatusCode::Success,
            wasm_state.get_response_bytes(),
        ))
    }
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
        "tf_model_get_shape" => (
            TF_MODEL_GET_SHAPE,
            wasmi::Signature::new(
                &[
                    ABI_USIZE, // shape_ptr_ptr
                    ABI_USIZE, // shape_len_ptr
                ][..],
                Some(ValueType::I32),
            ),
        ),
        "tf_model_infer" => (
            TF_MODEL_INFER,
            wasmi::Signature::new(
                &[
                    ABI_USIZE, // input_ptr
                    ABI_USIZE, // input_len
                    ABI_USIZE, // inference_ptr_ptr
                    ABI_USIZE, // inference_len_ptr
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

/// Converts a binary sequence to a string if it is a valid UTF-8 string, or formats it as a numeric
/// vector of bytes otherwise.
pub fn format_bytes(v: &[u8]) -> String {
    std::str::from_utf8(v)
        .map(|s| s.to_string())
        .unwrap_or_else(|_| format!("{:?}", v))
}
