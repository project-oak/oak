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

use crate::{logger::Logger, OakFunctionsBoxedExtensionFactory};

use anyhow::Context;
use byteorder::{ByteOrder, LittleEndian};
use futures::future::FutureExt;
use log::Level;
use oak_functions_abi::proto::{
    ExtensionHandle, OakStatus, Request, Response, ServerPolicy, StatusCode,
};
use oak_functions_extension::OakApiNativeExtension;
use oak_logger::OakLogger;
use serde::Deserialize;
use std::{collections::HashMap, convert::TryInto, str, sync::Arc, time::Duration};
use wasmi::ValueType;

const MAIN_FUNCTION_NAME: &str = "main";
const ALLOC_FUNCTION_NAME: &str = "alloc";

/// Wasm host function index numbers for `wasmi` to map import names with. This numbering is not
/// exposed to the Wasm client. See <https://docs.rs/wasmi/0.6.2/wasmi/trait.Externals.html>
const READ_REQUEST: usize = 0;
const WRITE_RESPONSE: usize = 1;
const WRITE_LOG_MESSAGE: usize = 3;
const INVOKE: usize = 4;
const EXTENSION_INDEX_OFFSET: usize = 10;

// Type aliases for positions and offsets in Wasm linear memory. Any future 64-bit version
// of Wasm would use different types.
pub type AbiPointer = u32;
pub type AbiPointerOffset = u32;
// Type alias for the ExtensionHandle type, which has to be cast into a ExtensionHandle.
pub type AbiExtensionHandle = i32;
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
    /// A mapping of internal host functions to the corresponding BoxedExtension.
    /// TODO(#2715): Replace by a map from `ExtensionHandles` to `BoxedExtensions`.
    extensions_indices: HashMap<usize, Box<dyn OakApiNativeExtension>>,
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

    /// Read arguments for extension from memory of Wasm module.
    pub fn read_extension_args(
        &self,
        buf_ptr: AbiPointer,
        buf_len: AbiPointerOffset,
    ) -> Result<Vec<u8>, wasmi::Error> {
        self.get_memory().get(buf_ptr, buf_len as usize)
    }

    // Write result of extension to memory of Wasm module.
    pub fn write_extension_result(
        &mut self,
        result: Vec<u8>,
        result_ptr_ptr: AbiPointer,
        result_len_ptr: AbiPointer,
    ) -> Result<(), OakStatus> {
        let buf_ptr = self.alloc(result.len() as u32);
        self.write_buffer_to_wasm_memory(&result, buf_ptr)?;
        self.write_u32_to_wasm_memory(buf_ptr, result_ptr_ptr)?;
        self.write_u32_to_wasm_memory(result.len() as u32, result_len_ptr)?;
        Ok(())
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

    pub fn invoke_extension_with_handle(
        &mut self,
        handle: AbiExtensionHandle,
        request_ptr: AbiPointer,
        request_len: AbiPointerOffset,
        response_ptr_ptr: AbiPointer,
        response_len_ptr: AbiPointer,
    ) -> Result<(), OakStatus> {
        let handle: ExtensionHandle = ExtensionHandle::from_i32(handle).ok_or({
            self.log_error(&format!("Fail to convert handle from i32 {:?}.", handle));
            OakStatus::ErrInvalidHandle
        })?;

        let request = self
            .read_extension_args(request_ptr, request_len)
            .map_err(|err| {
                self.log_error(&format!(
                    "Handle {:?}: Unable to read input from guest memory: {:?}",
                    handle, err
                ));
                OakStatus::ErrInvalidArgs
            })?;

        let extension = self
            .extensions_indices
            .values_mut()
            .find(|extension| extension.get_handle() == handle)
            .ok_or({
                // TODO(#2715): Add logging, which will be easier when we have a lookup to
                // extension_indices.
                // self.log_error(&format!("Cannot find extension with handle {:?}.", handle));
                OakStatus::ErrInvalidHandle
            })?;
        let response = extension.invoke(request)?;
        self.write_extension_result(response, response_ptr_ptr, response_len_ptr)
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

impl wasmi::Externals for WasmState {
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
            WRITE_LOG_MESSAGE => from_oak_status_result(
                self.write_log_message(args.nth_checked(0)?, args.nth_checked(1)?),
            ),
            INVOKE => from_oak_status_result(self.invoke_extension_with_handle(
                args.nth_checked(0)?,
                args.nth_checked(1)?,
                args.nth_checked(2)?,
                args.nth_checked(3)?,
                args.nth_checked(4)?,
            )),

            // TODO(#2710), TODO(#2711), TODO(#2712): Remove the following code, once all extensions
            // are called via handles.
            _ => {
                // Careful: We assume that here for the ABI call the first two arguments are the
                // request (which is true). We will remove this, when we call every
                // extension through `invoke`. Here, args are off-by-one compared to
                // `invoke_extension_with_handle` because there `args[0]` is the handle.
                let request_ptr: AbiPointer = args.nth_checked(0)?;
                let request_len: AbiPointerOffset = args.nth_checked(1)?;

                let request = self
                    .read_extension_args(request_ptr, request_len)
                    .map_err(|err| {
                        self.log_error(&format!(
                            "Unable to read input from guest memory: {:?}",
                            err
                        ));
                        OakStatus::ErrInvalidArgs
                    });

                let extension = &mut self
                    .extensions_indices
                    .get_mut(&index)
                    .unwrap_or_else(|| panic!("Unimplemented function at {}", index));

                let result = match request {
                    Ok(request) => {
                        let response = extension.invoke(request);
                        match response {
                            Ok(response) => {
                                if !response.is_empty() {
                                    // Careful: We assume every ABI call which returns a non-emtpy
                                    // response provides these arguments
                                    // (which is true).
                                    let response_ptr_ptr: AbiPointer = args.nth_checked(2)?;
                                    let response_len_ptr: AbiPointer = args.nth_checked(3)?;
                                    self.write_extension_result(
                                        response,
                                        response_ptr_ptr,
                                        response_len_ptr,
                                    )
                                } else {
                                    Ok(())
                                }
                            }
                            Err(err) => Err(err),
                        }
                    }
                    Err(err) => Err(err),
                };
                from_oak_status_result(result)
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
        extensions_indices: HashMap<usize, Box<dyn OakApiNativeExtension>>,
        extensions_metadata: HashMap<String, (usize, wasmi::Signature)>,
    ) -> anyhow::Result<WasmState> {
        let mut abi = WasmState {
            request_bytes,
            response_bytes: vec![],
            instance: None,
            memory: None,
            logger,
            extensions_indices,
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
pub async fn apply_policy<F>(policy: ServerPolicy, function: F) -> anyhow::Result<Response>
where
    F: std::marker::Send + 'static + FnOnce() -> anyhow::Result<Response>,
{
    // Use tokio::spawn to actually run the tasks in parallel, for more accurate measurement
    // of time.
    let task = tokio::spawn(async move { function() });
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
    extension_factories: Arc<Vec<OakFunctionsBoxedExtensionFactory>>,
    logger: Logger,
}

impl WasmHandler {
    pub fn create(
        wasm_module_bytes: &[u8],
        extension_factories: Vec<OakFunctionsBoxedExtensionFactory>,
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

    fn init_wasm_state(&self, request_bytes: Vec<u8>) -> anyhow::Result<WasmState> {
        let mut extensions_indices = HashMap::new();
        let mut extensions_metadata = HashMap::new();

        for (ind, factory) in self.extension_factories.iter().enumerate() {
            let extension = factory.create()?;
            let (name, signature) = extension.get_metadata();
            extensions_indices.insert(ind + EXTENSION_INDEX_OFFSET, extension);
            extensions_metadata.insert(name, (ind + EXTENSION_INDEX_OFFSET, signature));
        }

        let wasm_state = WasmState::new(
            &self.module,
            request_bytes,
            self.logger.clone(),
            extensions_indices,
            extensions_metadata,
        )?;

        Ok(wasm_state)
    }

    pub fn handle_invoke(&self, request: Request) -> anyhow::Result<Response> {
        let request_bytes = request.body;
        let mut wasm_state = self.init_wasm_state(request_bytes)?;

        wasm_state.invoke();

        for (_, extension) in wasm_state.extensions_indices.iter_mut() {
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

#[cfg(test)]
mod tests {
    use oak_functions_abi::{TestingRequest, TestingResponse};

    use super::{
        super::{grpc::create_wasm_handler, testing::*},
        *,
    };

    #[tokio::test]
    async fn test_invoke_extension_with_invalid_handle() {
        let mut wasm_state = create_test_wasm_state();
        // Assumes there is no negative ExtensionHandle. The remaining arguments don't matter, hence
        // they are 0.
        let extension = wasm_state.invoke_extension_with_handle(-1, 0, 0, 0, 0);
        assert!(extension.is_err());
        assert_eq!(OakStatus::ErrInvalidHandle, extension.unwrap_err())
    }

    #[tokio::test]
    async fn test_find_extension_not_available() {
        let mut wasm_state = create_test_wasm_state();
        // Assumes we have no TF extension in our test wasm_state. The remaining arguments don't
        // matter, hence they are 0.
        let extension =
            wasm_state.invoke_extension_with_handle(ExtensionHandle::TfHandle as i32, 0, 0, 0, 0);
        assert!(extension.is_err());
        assert_eq!(OakStatus::ErrInvalidHandle, extension.unwrap_err())
    }

    #[tokio::test]
    async fn test_invoke_extension() {
        let mut wasm_state = create_test_wasm_state();

        // Assumes we have a Testing extension in our test wasm_state.
        let message = "Hello!".to_owned();
        let request = bincode::serialize(&TestingRequest::Echo(message.clone()))
            .expect("Failed to serialize request.");

        // Guess some memory addresses in linear Wasm memory to write the request to.
        let request_ptr: AbiPointer = 100;
        let result = wasm_state.write_buffer_to_wasm_memory(&request, request_ptr);
        assert!(result.is_ok());

        // Guess some memory addresses in linear Wasm memory to write the response to.
        let response_ptr_ptr: AbiPointer = 200;
        let response_len_ptr: AbiPointer = 250;

        let result = wasm_state.invoke_extension_with_handle(
            ExtensionHandle::TestingHandle as i32,
            request_ptr,
            request.len() as u32,
            response_ptr_ptr,
            response_len_ptr,
        );
        assert!(result.is_ok());

        let expected_response = bincode::serialize(&TestingResponse::Echo(message))
            .expect("Failed to serialize response.");

        // Get response_len from response_len_ptr.
        let response_len: AbiPointerOffset =
            LittleEndian::read_u32(&wasm_state.get_memory().get(response_len_ptr, 4).unwrap());

        // Assert that response_len holds length of expected response.
        assert_eq!(response_len as usize, expected_response.len());

        // Get response_ptr from resposne_ptr_ptr.
        let response_ptr: AbiPointer =
            LittleEndian::read_u32(&wasm_state.get_memory().get(response_ptr_ptr, 4).unwrap());

        // Assert that reponse_ptr holds expected response.
        assert_eq!(
            wasm_state
                .read_buffer_from_wasm_memory(response_ptr, response_len)
                .unwrap(),
            expected_response
        );
    }

    fn create_test_wasm_state() -> WasmState {
        let logger = Logger::for_test();

        let testing_factory = TestingFactory::new_boxed_extension_factory(logger.clone())
            .expect("Could not create TestingFactory.");

        let wasm_module_bytes = test_utils::create_echo_wasm_module_bytes();

        let wasm_handler = create_wasm_handler(&wasm_module_bytes, vec![testing_factory], logger)
            .expect("Could not create WasmHandler.");
        wasm_handler
            .init_wasm_state(b"".to_vec())
            .expect("Could not create WasmState.")
    }
}
