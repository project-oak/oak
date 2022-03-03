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
use async_trait::async_trait;
use byteorder::{ByteOrder, LittleEndian};
use futures::future::FutureExt;
use log::Level;
use oak_functions_abi::proto::{
    ChannelHandle, ChannelStatus, OakStatus, Request, Response, ServerPolicy, StatusCode,
};
use oak_logger::OakLogger;
use serde::Deserialize;
use std::{collections::HashMap, convert::TryInto, str, sync::Arc, time::Duration};
use tokio::sync::mpsc::{
    channel,
    error::{TryRecvError, TrySendError},
    Receiver, Sender,
};
use wasmi::ValueType;

const MAIN_FUNCTION_NAME: &str = "main";
const ALLOC_FUNCTION_NAME: &str = "alloc";

/// Wasm host function index numbers for `wasmi` to map import names with. This numbering is not
/// exposed to the Wasm client. See <https://docs.rs/wasmi/0.6.2/wasmi/trait.Externals.html>
const READ_REQUEST: usize = 0;
const WRITE_RESPONSE: usize = 1;
const WRITE_LOG_MESSAGE: usize = 3;
const CHANNEL_READ: usize = 4;
const CHANNEL_WRITE: usize = 5;
const EXTENSION_INDEX_OFFSET: usize = 10;

// Type alias for a message sent over a channel through UWABI.
pub type UwabiMessage = Vec<u8>;

// Bound on the amount of [`UwabiMessage`]s an [`Endpoint`] can hold on the sender and the
// receiver individually. We fixed 100 arbitrarily, and it is the same for every Endpoint. We expect
// UwabiMessages to be processed fast and do not expect to exceed the bound.
const UWABI_CHANNEL_BOUND: usize = 100;

// Type aliases for positions and offsets in Wasm linear memory. Any future 64-bit version
// of Wasm would use different types.
pub type AbiPointer = u32;
pub type AbiPointerOffset = u32;
// Type alias for the ChannelHandle type, which has to be cast into a ChannelHandle.
pub type AbiChannelHandle = i32;
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

/// A BoxedExtension can either be a `Native extension called by a dedicated ABI function, or a
/// `Uwabi` extension called by listening to a channel.
pub enum BoxedExtension {
    Native(Box<dyn OakApiNativeExtension + Send + Sync>),
    Uwabi(Box<dyn UwabiExtension>),
}

pub type BoxedExtensionFactory = Box<dyn ExtensionFactory + Send + Sync>;

/// Trait for implementing an extension which relies on UWABI.
#[async_trait]
pub trait UwabiExtension: Sync + Send {
    /// Get the channel handle to address this extension.
    fn get_channel_handle(&self) -> ChannelHandle;

    /// Get the endpoint.
    // TODO(#2508): Stop exposing the endpoint for an extension as soon as we have a way the
    // extension handles how it reads/writes into the endpoint.
    fn get_endpoint_mut(&mut self) -> &mut Endpoint;

    /// Set the endpoint if it has not been set before.
    // TODO(#2510) We cannot set the endpoint when we `create` the extension, as this would require
    // to change the `BoxedExtensionFactory` trait. This helps to keep the changes to the
    // (existing) Native extensions minimal.
    fn set_endpoint(&mut self, endpoint: Endpoint);

    // Run an UWABI extension by continously receiving messages on the endpoint and answering it.
    async fn run(self: Box<Self>);
}

/// `WasmState` holds runtime values for a particular execution instance of Wasm, handling a
/// single user request. The methods here correspond to the ABI host functions that allow the Wasm
/// module to exchange the request and the response with the Oak functions server. These functions
/// translate values between Wasm linear memory and Rust types.
#[allow(dead_code)]
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
    /// A mapping from channel handles to the hosted endpoints of channels.
    channel_switchboard: ChannelSwitchboard,
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
    fn validate_range(
        &self,
        addr: AbiPointer,
        offset: AbiPointerOffset,
    ) -> Result<(), ChannelStatus> {
        let memory_size: wasmi::memory_units::Bytes = self.get_memory().current_size().into();
        // Check whether the end address is below or equal to the size of the guest memory.
        if wasmi::memory_units::Bytes((addr as usize) + (offset as usize)) <= memory_size {
            Ok(())
        } else {
            Err(ChannelStatus::ChannelInvalidArgs)
        }
    }

    /// Reads the buffer starting at address `buf_ptr` with length `buf_len` from the Wasm memory.
    pub fn read_buffer_from_wasm_memory(
        &self,
        buf_ptr: AbiPointer,
        buf_len: AbiPointerOffset,
    ) -> Result<Vec<u8>, ChannelStatus> {
        self.get_memory()
            .get(buf_ptr, buf_len as usize)
            .map_err(|err| {
                self.logger.log_sensitive(
                    Level::Error,
                    &format!("Unable to read buffer from guest memory: {:?}", err),
                );
                ChannelStatus::ChannelInvalidArgs
            })
    }

    /// Writes the buffer `source` at the address `dest` of the Wasm memory, if `source` fits in the
    /// allocated memory.
    pub fn write_buffer_to_wasm_memory(
        &self,
        source: &[u8],
        dest: AbiPointer,
    ) -> Result<(), ChannelStatus> {
        self.validate_range(dest, source.len() as u32)?;
        self.get_memory().set(dest, source).map_err(|err| {
            self.logger.log_sensitive(
                Level::Error,
                &format!("Unable to write buffer into guest memory: {:?}", err),
            );
            ChannelStatus::ChannelInvalidArgs
        })
    }

    ///  Writes the u32 `value` at the `address` of the Wasm memory.
    pub fn write_u32_to_wasm_memory(
        &self,
        value: u32,
        address: AbiPointer,
    ) -> Result<(), ChannelStatus> {
        let value_bytes = &mut [0; 4];
        LittleEndian::write_u32(value_bytes, value);
        self.get_memory().set(address, value_bytes).map_err(|err| {
            self.logger.log_sensitive(
                Level::Error,
                &format!("Unable to write u32 value into guest memory: {:?}", err),
            );
            ChannelStatus::ChannelInvalidArgs
        })
    }

    /// Writes the given `buffer` by allocating `buffer.len()` Wasm memory and writing the address
    /// of the allocated memory to `dest_ptr_ptr` and the length to `dest_len_ptr`.
    pub fn alloc_and_write_buffer_to_wasm_memory(
        &mut self,
        buffer: Vec<u8>,
        dest_ptr_ptr: AbiPointer,
        dest_len_ptr: AbiPointer,
    ) -> Result<(), ChannelStatus> {
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

    // Helper function to get the hosted Endpoint for the given channel handle.
    fn get_endpoint_from_channel_handle(
        &mut self,
        channel_handle: AbiChannelHandle,
    ) -> Result<&mut Endpoint, ChannelStatus> {
        let channel_handle =
            ChannelHandle::from_i32(channel_handle).ok_or(ChannelStatus::ChannelHandleInvalid)?;
        let endpoint = self
            .channel_switchboard
            .get_mut(&channel_handle)
            .ok_or(ChannelStatus::ChannelHandleInvalid)?;
        Ok(endpoint)
    }

    pub fn channel_read(
        &mut self,
        channel_handle: AbiChannelHandle,
        dest_ptr_ptr: AbiPointer,
        dest_len_ptr: AbiPointer,
    ) -> Result<(), ChannelStatus> {
        // Read message from channel at channel_handle.
        let endpoint = self.get_endpoint_from_channel_handle(channel_handle)?;
        let receiver = &mut endpoint.receiver;
        let message = receiver.try_recv().map_err(|e| match e {
            TryRecvError::Empty => ChannelStatus::ChannelEmpty,
            TryRecvError::Disconnected => ChannelStatus::ChannelEndpointDisconnected,
        })?;

        // Write message to memory of the Wasm module.
        self.alloc_and_write_buffer_to_wasm_memory(message, dest_ptr_ptr, dest_len_ptr)?;

        Ok(())
    }

    pub fn channel_write(
        &mut self,
        channel_handle: AbiChannelHandle,
        src_buf_ptr: AbiPointer,
        src_buf_len: AbiPointerOffset,
    ) -> Result<(), ChannelStatus> {
        // Read message from Wasm memory.
        let message: UwabiMessage = self.read_buffer_from_wasm_memory(src_buf_ptr, src_buf_len)?;

        // Write message to hosted endpoint.
        let endpoint = self.get_endpoint_from_channel_handle(channel_handle)?;
        let sender = &mut endpoint.sender;

        sender.try_send(message).map_err(|e| match e {
            TrySendError::Full(_) => ChannelStatus::ChannelFull,
            TrySendError::Closed(_) => ChannelStatus::ChannelEndpointClosed,
        })?;

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
            CHANNEL_READ => from_channel_status_result(self.channel_read(
                args.nth_checked(0)?,
                args.nth_checked(1)?,
                args.nth_checked(2)?,
            )),
            CHANNEL_WRITE => from_channel_status_result(self.channel_write(
                args.nth_checked(0)?,
                args.nth_checked(1)?,
                args.nth_checked(2)?,
            )),

            _ => {
                let mut extensions_indices = self
                    .extensions_indices
                    .take()
                    .expect("no extensions_indices is set");
                let extension = match extensions_indices.get_mut(&index) {
                    Some(BoxedExtension::Native(extension)) => Box::new(extension),
                    Some(BoxedExtension::Uwabi(_)) => {
                        panic!("Invoked Uwabi extension at index {} instead of reading/writing from channel.", index)
                    }
                    None => panic!("Unimplemented function at {}", index),
                };
                let result = from_oak_status_result(extension.invoke(self, args)?);
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
        channel_switchboard: ChannelSwitchboard,
    ) -> anyhow::Result<WasmState> {
        let mut abi = WasmState {
            request_bytes,
            response_bytes: vec![],
            instance: None,
            memory: None,
            logger,
            extensions_indices: Some(extensions_indices),
            extensions_metadata,
            channel_switchboard,
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

    fn init_wasm_state_and_extensions(
        &self,
        request_bytes: Vec<u8>,
    ) -> anyhow::Result<(WasmState, Vec<Box<dyn UwabiExtension>>)> {
        let mut extensions_indices = HashMap::new();
        let mut extensions_metadata = HashMap::new();
        let mut uwabi_extensions: Vec<Box<dyn UwabiExtension>> = vec![];

        let mut channel_switchboard = ChannelSwitchboard::new();

        for (ind, factory) in self.extension_factories.iter().enumerate() {
            let extension = factory.create()?;
            match extension {
                BoxedExtension::Native(ref native_extension) => {
                    let (name, signature) = native_extension.get_metadata();
                    extensions_indices.insert(ind + EXTENSION_INDEX_OFFSET, extension);
                    extensions_metadata.insert(name, (ind + EXTENSION_INDEX_OFFSET, signature));
                }
                BoxedExtension::Uwabi(mut uwabi_extension) => {
                    let channel_handle = uwabi_extension.get_channel_handle();
                    let endpoint = channel_switchboard.register(channel_handle);
                    uwabi_extension.set_endpoint(endpoint);
                    uwabi_extensions.push(uwabi_extension);
                }
            }
        }

        let wasm_state = WasmState::new(
            &self.module,
            request_bytes,
            self.logger.clone(),
            extensions_indices,
            extensions_metadata,
            channel_switchboard,
        )?;

        Ok((wasm_state, uwabi_extensions))
    }

    pub async fn handle_invoke(&self, request: Request) -> anyhow::Result<Response> {
        let request_bytes = request.body;
        let (mut wasm_state, uwabi_extensions) =
            self.init_wasm_state_and_extensions(request_bytes)?;

        for uwabi_extension in uwabi_extensions {
            tokio::spawn(uwabi_extension.run());
        }

        wasm_state.invoke();
        for extension in wasm_state
            .extensions_indices
            .take()
            .expect("no extensions_indices is set in wasm_state")
            .into_values()
        {
            if let BoxedExtension::Native(mut native_extension) = extension {
                native_extension.terminate()?;
            }
        }

        Ok(Response::create(
            StatusCode::Success,
            wasm_state.get_response_bytes(),
        ))

        // Here we drop all endpoints of the Wasm module (i.e., the wasm_state.channel_switchboard).
        // This indicates to the endpoints in the UWABI Extensions that they will not receive
        // further messages and can stop. Note, that we do not do a clean shutdown of the receivers
        // in the endpoints Wasm module, because there is no need to handle, or even log,
        // the remaining messages.
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
        "channel_read" => (
            CHANNEL_READ,
            wasmi::Signature::new(
                &[
                    ABI_USIZE, // channel_handle
                    ABI_USIZE, // dest_buf_ptr_ptr
                    ABI_USIZE, // dest_buf_len_ptr
                ][..],
                Some(ValueType::I32),
            ),
        ),
        "channel_write" => (
            CHANNEL_WRITE,
            wasmi::Signature::new(
                &[
                    ABI_USIZE, // channel_handle
                    ABI_USIZE, // src_buf_ptr
                    ABI_USIZE, // src_buf_len
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

/// A helper function to move between our specific result type `Result<(), ChannelStatus>` and the
/// `wasmi` specific result type `Result<Option<wasmi::RuntimeValue>, wasmi::Trap>`, mapping:
/// - `Ok(())` to `Ok(Some(ChannelStatus::Ok))`
/// - `Err(x)` to `Ok(Some(x))`
fn from_channel_status_result(
    result: Result<(), ChannelStatus>,
) -> Result<Option<wasmi::RuntimeValue>, wasmi::Trap> {
    let channel_status_from_result =
        result.map_or_else(|x: ChannelStatus| x, |()| ChannelStatus::ChannelOk);
    let wasmi_value = wasmi::RuntimeValue::I32(channel_status_from_result as i32);
    Ok(Some(wasmi_value))
}

/// Converts a binary sequence to a string if it is a valid UTF-8 string, or formats it as a numeric
/// vector of bytes otherwise.
pub fn format_bytes(v: &[u8]) -> String {
    std::str::from_utf8(v)
        .map(|s| s.to_string())
        .unwrap_or_else(|_| format!("{:?}", v))
}

// The Endpoint of a bidirectional channel.
#[derive(Debug)]
pub struct Endpoint {
    sender: Sender<UwabiMessage>,
    receiver: Receiver<UwabiMessage>,
}

/// Create a channel with two symmetrical endpoints. The [`UwabiMessage`] sent from one [`Endpoint`]
/// are received at the other [`Endpoint`] and vice versa by connecting two unidirectional
/// [tokio::mpsc channels](https://docs.rs/tokio/0.1.16/tokio/sync/mpsc/index.html).
///
/// In ASCII art:
///
/// ```text
///   sender ____  ____ sender
///              \/
/// receiver ____/\____ receiver
/// ```
fn channel_create() -> (Endpoint, Endpoint) {
    let (tx0, rx0) = channel::<UwabiMessage>(UWABI_CHANNEL_BOUND);
    let (tx1, rx1) = channel::<UwabiMessage>(UWABI_CHANNEL_BOUND);
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
struct ChannelSwitchboard(HashMap<ChannelHandle, Endpoint>);

impl ChannelSwitchboard {
    fn new() -> Self {
        ChannelSwitchboard(HashMap::new())
    }

    // Creates a channel for `channel_handle`, adds one endpoint to the channel switchboard and
    // returns the corresponding endpoint. Overwrites existing channels for `channel_handle`.
    fn register(&mut self, channel_handle: ChannelHandle) -> Endpoint {
        let (e1, e2) = channel_create();
        self.0.insert(channel_handle, e2);
        e1
    }

    // Get the endpoint registered for the channel_handle. To send to/receive from the endpoint, the
    // endpoint has to be mutable.
    fn get_mut(&mut self, channel_handle: &ChannelHandle) -> Option<&mut Endpoint> {
        self.0.get_mut(channel_handle)
    }
}

#[cfg(test)]
mod tests {
    use super::{super::grpc::create_wasm_handler, *};
    use serde::{Deserialize, Serialize};
    pub struct TestingFactory {
        logger: Logger,
    }

    impl TestingFactory {
        pub fn new_boxed_extension_factory(
            logger: Logger,
        ) -> anyhow::Result<BoxedExtensionFactory> {
            Ok(Box::new(Self { logger }))
        }
    }

    impl ExtensionFactory for TestingFactory {
        fn create(&self) -> anyhow::Result<BoxedExtension> {
            let extension = TestingExtension {
                logger: self.logger.clone(),
                endpoint: None,
            };
            Ok(BoxedExtension::Uwabi(Box::new(extension)))
        }
    }

    #[allow(dead_code)]
    pub struct TestingExtension {
        logger: Logger,
        endpoint: Option<Endpoint>,
    }

    #[derive(Serialize, Deserialize)]
    // Note that currently the caller is responsible that the Request is send to the extension, and
    // the extension responds with the response.
    enum TestingMessage {
        EchoRequest(String),
        EchoResponse(String),
    }

    #[async_trait]
    impl UwabiExtension for TestingExtension {
        fn get_channel_handle(&self) -> oak_functions_abi::proto::ChannelHandle {
            ChannelHandle::Testing
        }

        fn get_endpoint_mut(&mut self) -> &mut Endpoint {
            match &mut self.endpoint {
                Some(endpoint) => endpoint,
                None => panic!("No endpoint set for extension"),
            }
        }

        fn set_endpoint(&mut self, endpoint: Endpoint) {
            if self.endpoint.is_none() {
                self.endpoint = Some(endpoint);
            }
        }

        async fn run(mut self: Box<Self>) {
            let endpoint = self.get_endpoint_mut();
            let receiver = &mut endpoint.receiver;
            let sender = &mut endpoint.sender;

            // The runtime endpoint continiously reads messages from the Wasm module endpoint until
            // all senders from the Wasm endpoint are closed.
            //
            // If the Testing Message is not an expected request, the Testing Extension panics.
            while let Some(request) = receiver.recv().await {
                let deserialized_testing_message =
                    bincode::deserialize(&request).expect("Fail to deserialize testing message.");
                match deserialized_testing_message {
                    TestingMessage::EchoRequest(echo_message) => {
                        let echo_response = TestingMessage::EchoResponse(echo_message);
                        let serialized_echo_response = bincode::serialize(&echo_response)
                            .expect("Fail to serialize testing message.");
                        let result = sender.send(serialized_echo_response).await;
                        assert!(result.is_ok())
                    }
                    _ => panic!("Unexpected Testing Message: {:?}", request),
                }
            }
        }
    }

    #[test]
    fn test_start_from_empty_endpoints() {
        fn check_empty(endpoint: &mut Endpoint) {
            let receiver = &mut endpoint.receiver;
            assert_eq!(TryRecvError::Empty, receiver.try_recv().unwrap_err());
        }
        let (mut module, mut runtime) = channel_create();
        check_empty(&mut module);
        check_empty(&mut runtime);
    }

    #[tokio::test]
    async fn test_crossed_write_read() {
        async fn check_crossed_write_read(endpoint1: &mut Endpoint, endpoint2: &mut Endpoint) {
            let message: UwabiMessage = vec![42, 21, 0];
            let sender = &endpoint1.sender;
            let send_result = sender.send(message.clone()).await;
            assert!(send_result.is_ok());

            let receiver = &mut endpoint2.receiver;
            let received_message = receiver.recv().await.unwrap();

            assert_eq!(message, received_message);
        }

        let (mut endpoint_1, mut endpoint_2) = channel_create();
        // Check from endpoint_1 to endpoint_2.
        check_crossed_write_read(&mut endpoint_1, &mut endpoint_2).await;
        // Check the other direction from endpoint_2 to endpoint_1.
        check_crossed_write_read(&mut endpoint_2, &mut endpoint_1).await;
    }

    #[tokio::test]
    async fn test_create_channel_switchboard_in_wasm_state() {
        let (wasm_state, _) = create_test_wasm_state_and_extensions();
        let mut channel_switchboard = wasm_state.channel_switchboard;

        assert!(&channel_switchboard
            .get_mut(&ChannelHandle::Unspecified)
            .is_none());

        assert!(&channel_switchboard
            .get_mut(&ChannelHandle::Testing)
            .is_some());
    }

    #[tokio::test]
    async fn test_get_endpoint_from_channel_handle_out_of_range() {
        let (mut wasm_state, _) = create_test_wasm_state_and_extensions();
        let result = wasm_state.get_endpoint_from_channel_handle(-1);
        assert!(result.is_err());
        assert_eq!(ChannelStatus::ChannelHandleInvalid, result.unwrap_err())
    }

    #[tokio::test]
    async fn test_get_endpoint_from_channel_handle_without_endpoint() {
        let (mut wasm_state, _) = create_test_wasm_state_and_extensions();
        // Assumes ChannelHandle 0 will never have an Endpoint.
        let result = wasm_state.get_endpoint_from_channel_handle(0);
        assert!(result.is_err());
        assert_eq!(ChannelStatus::ChannelHandleInvalid, result.unwrap_err())
    }

    #[tokio::test]
    async fn test_drop_channel_switchboard_stops_recv() {
        let mut channel_switchboard = ChannelSwitchboard::new();
        let mut endpoint_2 = channel_switchboard.register(ChannelHandle::Testing);

        let stopped_receiving = tokio::spawn(async move {
            endpoint_2.receiver.recv().await;
            true
        });

        std::mem::drop(channel_switchboard);
        assert!(stopped_receiving.await.unwrap());
    }

    #[tokio::test]
    async fn test_hosted_channel_read_no_message() {
        let channel_handle = ChannelHandle::Testing as i32;
        let (mut wasm_state, _uwabi_extensions) = create_test_wasm_state_and_extensions();
        let result = wasm_state.channel_read(channel_handle, 0, 0);
        assert!(result.is_err());
        assert_eq!(ChannelStatus::ChannelEmpty, result.unwrap_err());
    }

    #[tokio::test]
    async fn test_hosted_channel_read_channel_closed() {
        let channel_handle = ChannelHandle::Testing;
        let (mut wasm_state, mut uwabi_extensions) = create_test_wasm_state_and_extensions();
        // Drop all extensions to close the runtime endpoint of the channels.
        uwabi_extensions.clear();
        let result = wasm_state.channel_read(channel_handle as i32, 0, 0);
        assert!(result.is_err());
        assert_eq!(
            ChannelStatus::ChannelEndpointDisconnected,
            result.unwrap_err()
        );
    }

    #[tokio::test]
    async fn test_hosted_channel_read_ok() {
        let channel_handle = ChannelHandle::Testing;
        let message = vec![42, 42, 232];
        let (mut wasm_state, mut uwabi_extensions) = create_test_wasm_state_and_extensions();
        let mut testing_extension =
            extension_for_channel_handle(&mut uwabi_extensions, channel_handle);

        write_to_runtime_endpoint(&mut testing_extension, message.clone()).await;

        // Guess some memory addresses in linear Wasm memory.
        let dest_ptr_ptr: AbiPointer = 100;
        let dest_len_ptr: AbiPointer = 150;

        let result = wasm_state.channel_read(channel_handle as i32, dest_ptr_ptr, dest_len_ptr);
        assert!(result.is_ok());

        // Get dest_len from dest_len_ptr.
        let dest_len: u32 =
            LittleEndian::read_u32(&wasm_state.get_memory().get(dest_len_ptr, 4).unwrap());

        // Assert that dest_len holds length of message.
        assert_eq!(dest_len as usize, message.len());

        // Get dest_ptr from dest_ptr_ptr.
        let dest_ptr: u32 =
            LittleEndian::read_u32(&wasm_state.get_memory().get(dest_ptr_ptr, 4).unwrap());

        // Assert that dest_ptr holds message.
        assert_eq!(
            wasm_state
                .read_buffer_from_wasm_memory(dest_ptr, dest_len)
                .unwrap(),
            message
        );
    }

    #[tokio::test]
    async fn test_hosted_channel_write_ok() {
        let channel_handle = ChannelHandle::Testing;
        let message: String = String::from("Test Message");
        let (mut wasm_state, mut uwabi_extensions) = create_test_wasm_state_and_extensions();
        let testing_extension = extension_for_channel_handle(&mut uwabi_extensions, channel_handle);

        let join_handle = tokio::spawn(testing_extension.run());

        // Guess some memory addresses in linear Wasm memory to write the message to.
        let src_buf_ptr: AbiPointer = 100;

        let echo_request = TestingMessage::EchoRequest(message.clone());
        let serialized_echo_request =
            bincode::serialize(&echo_request).expect("Fail to serialize testing message.");
        let result = wasm_state.write_buffer_to_wasm_memory(&serialized_echo_request, src_buf_ptr);
        assert!(result.is_ok());

        // The Wasm Module writes an ECHO message to the Testing Extension.
        let result = wasm_state.channel_write(
            channel_handle as i32,
            src_buf_ptr,
            serialized_echo_request.len() as u32,
        );
        assert!(result.is_ok());

        // The Testing Extension should now ECHO the message to the Wasm module so we read from then
        // Wasm module endpoint.
        let echo_response = read_from_wasm_module_endpoint(&mut wasm_state, channel_handle).await;

        let deserialized_response =
            bincode::deserialize(&echo_response).expect("Fail to deserialize testing message.");

        if let TestingMessage::EchoResponse(echoed_message) = deserialized_response {
            assert_eq!(echoed_message, message)
        } else {
            panic!("Deserialzed message not a valid message")
        }

        // Dropping the WasmState drops the Channel Switchboard stopping the extension.
        std::mem::drop(wasm_state);

        let result = join_handle.await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_hosted_channel_write_full() {
        let channel_handle = ChannelHandle::Testing;
        let message: UwabiMessage = vec![42, 42];
        let (mut wasm_state, _uwabi_extensions) = create_test_wasm_state_and_extensions();

        // Guess some memory addresses in linear Wasm memory to write the message to.
        let src_buf_ptr: AbiPointer = 100;
        let result = wasm_state.write_buffer_to_wasm_memory(&message, src_buf_ptr);
        assert!(result.is_ok());

        // Write the message UWABI_CHANNEL_BOUND times.
        for _ in 0..UWABI_CHANNEL_BOUND {
            let result =
                wasm_state.channel_write(channel_handle as i32, src_buf_ptr, message.len() as u32);
            assert!(result.is_ok());
        }

        let result =
            wasm_state.channel_write(channel_handle as i32, src_buf_ptr, message.len() as u32);
        assert!(result.is_err());
        assert_eq!(ChannelStatus::ChannelFull, result.unwrap_err());
    }

    #[tokio::test]
    async fn test_hosted_channel_write_channel_closed() {
        let channel_handle = ChannelHandle::Testing;
        let (mut wasm_state, mut uwabi_extensions) = create_test_wasm_state_and_extensions();
        // Drop all extensions to close the runtime endpoint of the channels.
        uwabi_extensions.clear();
        let result = wasm_state.channel_write(channel_handle as i32, 0, 0);
        assert!(result.is_err());
        assert_eq!(ChannelStatus::ChannelEndpointClosed, result.unwrap_err());
    }

    fn create_test_wasm_handler() -> WasmHandler {
        let logger = Logger::for_test();

        let testing_factory = TestingFactory::new_boxed_extension_factory(logger.clone())
            .expect("Could not create TestingFactory.");

        let wasm_module_bytes = test_utils::create_echo_wasm_module_bytes();

        create_wasm_handler(&wasm_module_bytes, vec![testing_factory], logger)
            .expect("could not create wasm_handler")
    }

    fn create_test_wasm_state_and_extensions() -> (WasmState, Vec<Box<dyn UwabiExtension>>) {
        let wasm_handler = create_test_wasm_handler();
        wasm_handler
            .init_wasm_state_and_extensions(b"".to_vec())
            .expect("could not create wasm_state")
    }

    // Helper function for testing to write to the endpoint of the given UWABI Extension.
    async fn write_to_runtime_endpoint(
        uwabi_extension: &mut Box<dyn UwabiExtension>,
        message: UwabiMessage,
    ) {
        let endpoint = uwabi_extension.get_endpoint_mut();
        let result = endpoint.sender.send(message.to_vec().clone()).await;
        assert!(result.is_ok());
    }

    // Helper function for testing to read from the endpoint associated to ChannelHandle in the Wasm
    // Module.
    async fn read_from_wasm_module_endpoint(
        wasm_state: &mut WasmState,
        channel_handle: ChannelHandle,
    ) -> UwabiMessage {
        wasm_state
            .channel_switchboard
            .get_mut(&channel_handle)
            .expect("Endpoint not set for Channel Handle")
            .receiver
            .recv()
            .await
            .expect("No message or channel closed.")
    }

    // Helper function for testing to find the Extension associated to ChannelHandle.
    fn extension_for_channel_handle(
        uwabi_extensions: &mut Vec<Box<dyn UwabiExtension>>,
        channel_handle: ChannelHandle,
    ) -> Box<dyn UwabiExtension> {
        let pos_of_extension = uwabi_extensions
            .iter()
            .position(|uwabi_extension| {
                let channel_handle_of_extension = uwabi_extension.get_channel_handle();
                channel_handle_of_extension == channel_handle
            })
            .expect("No extension for channel handle.");
        uwabi_extensions.remove(pos_of_extension)
    }
}
