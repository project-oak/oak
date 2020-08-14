//
// Copyright 2020 The Project Oak Authors
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

//! WebAssembly Node functionality.

use crate::{node::ConfigurationError, NodeMessage, NodePrivilege, NodeReadStatus, RuntimeProxy};
use byteorder::{ByteOrder, LittleEndian};
use log::{debug, error, info, trace, warn};
use maplit::hashset;
use oak_abi::{
    label::Label,
    proto::oak::application::{
        ApplicationConfiguration, NodeConfiguration, WebAssemblyConfiguration,
    },
    OakStatus,
};
use prost::Message as _;
use rand::RngCore;
use sha2::digest::Digest;
use std::{string::String, sync::Arc};
use tokio::sync::oneshot;
use wasmi::ValueType;

#[cfg(test)]
mod tests;

/// Wasm host function index numbers for `wasmi` to map import names with.  This numbering is not
/// exposed to the Wasm client.  See https://docs.rs/wasmi/0.6.2/wasmi/trait.Externals.html
const NODE_CREATE: usize = 0;
const RANDOM_GET: usize = 1;
const CHANNEL_CLOSE: usize = 2;
const CHANNEL_CREATE: usize = 3;
const CHANNEL_WRITE: usize = 4;
const CHANNEL_READ: usize = 5;
const WAIT_ON_CHANNELS: usize = 6;
// TODO(#817): remove this; we shouldn't need to have WASI stubs.
const WASI_STUB: usize = 7;

// Type aliases for positions and offsets in Wasm linear memory. Any future 64-bit version
// of Wasm would use different types.
type AbiPointer = u32;
type AbiPointerOffset = u32;
/// Wasm type identifier for position/offset values in linear memory.  Any future 64-bit version of
/// Wasm would use a different value.
const ABI_USIZE: ValueType = ValueType::I32;

/// `WasmInterface` holds runtime values for a particular execution instance of Wasm, running a
/// single Oak Wasm Node.  The methods here that correspond to the Oak ABI host functions are
/// wrappers around the equivalent methods in `RuntimeProxy`, translating values between Wasm linear
/// memory and Rust types.
struct WasmInterface {
    /// A per-instance Node name for pretty printing.
    pretty_name: String,

    /// A reference to the memory used by the `wasmi` interpreter. Host ABI functions using Wasm
    /// relative addresses will perform reads/writes against this reference.
    memory: Option<wasmi::MemoryRef>,

    runtime: RuntimeProxy,
}

impl WasmInterface {
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

    /// Creates a new `WasmInterface` structure.
    pub fn new(pretty_name: &str, runtime: RuntimeProxy) -> WasmInterface {
        WasmInterface {
            pretty_name: pretty_name.to_string(),
            memory: None,
            runtime,
        }
    }

    /// Corresponds to the host ABI function [`node_create`](https://github.com/project-oak/oak/blob/main/docs/abi.md#node_create).
    #[allow(clippy::too_many_arguments)]
    fn node_create(
        &self,
        config_ptr: AbiPointer,
        config_length: AbiPointerOffset,
        label_ptr: AbiPointer,
        label_length: AbiPointerOffset,
        initial_handle: oak_abi::Handle,
    ) -> Result<(), OakStatus> {
        trace!(
            "{}: node_create({}, {}, {})",
            self.pretty_name,
            config_ptr,
            config_length,
            initial_handle
        );

        if self.runtime.is_terminating() {
            debug!("{}: node_create() returning terminated", self.pretty_name);
            return Err(OakStatus::ErrTerminated);
        }

        let config_bytes = self
            .get_memory()
            .get(config_ptr, config_length as usize)
            .map_err(|err| {
                error!(
                    "{}: node_create(): Unable to read config from guest memory: {:?}",
                    self.pretty_name, err
                );
                OakStatus::ErrInvalidArgs
            })?;

        let config = NodeConfiguration::decode(config_bytes.as_ref()).map_err(|err| {
            warn!(
                "{}: node_create(): Could not parse node configuration: {:?}",
                self.pretty_name, err
            );
            OakStatus::ErrInvalidArgs
        })?;

        let label_bytes = self
            .get_memory()
            .get(label_ptr, label_length as usize)
            .map_err(|err| {
                error!(
                    "{}: node_create(): Unable to read label from guest memory: {:?}",
                    self.pretty_name, err
                );
                OakStatus::ErrInvalidArgs
            })?;
        let label = Label::deserialize(&label_bytes).ok_or_else(|| {
            error!(
                "{}: node_create: could not deserialize label",
                self.pretty_name
            );
            OakStatus::ErrInvalidArgs
        })?;

        self.runtime
            .node_create(&config, &label, initial_handle)
            .map_err(|err| {
                error!(
                    "{}: node_create(): Could not create node: {:?}",
                    self.pretty_name, err
                );
                err
            })
    }

    /// Corresponds to the host ABI function [`random_get`](https://github.com/project-oak/oak/blob/main/docs/abi.md#random_get).
    fn random_get(&self, dest: AbiPointer, dest_length: AbiPointerOffset) -> Result<(), OakStatus> {
        debug!(
            "{}: random_get({}, {})",
            self.pretty_name, dest, dest_length
        );

        self.validate_ptr(dest, dest_length)?;

        let dest = dest as usize;
        let dest_length = dest_length as usize;

        self.get_memory().with_direct_access_mut(|memory| {
            rand::thread_rng().fill_bytes(&mut memory[dest..(dest + dest_length)]);
        });

        Ok(())
    }

    /// Corresponds to the host ABI function [`channel_close`](https://github.com/project-oak/oak/blob/main/docs/abi.md#channel_close).
    fn channel_close(&mut self, handle: oak_abi::Handle) -> Result<(), OakStatus> {
        self.runtime.channel_close(handle)
    }

    /// Corresponds to the host ABI function [`channel_create`](https://github.com/project-oak/oak/blob/main/docs/abi.md#channel_create).
    fn channel_create(
        &mut self,
        write_addr: AbiPointer,
        read_addr: AbiPointer,
        label_ptr: AbiPointer,
        label_length: AbiPointerOffset,
    ) -> Result<(), OakStatus> {
        trace!(
            "{}: channel_create({}, {}, {}, {})",
            self.pretty_name,
            write_addr,
            read_addr,
            label_ptr,
            label_length
        );

        if self.runtime.is_terminating() {
            debug!("{} returning terminated", self.pretty_name);
            return Err(OakStatus::ErrTerminated);
        }

        self.validate_ptr(write_addr, 8)?;
        self.validate_ptr(read_addr, 8)?;

        let label_bytes = self
            .get_memory()
            .get(label_ptr, label_length as usize)
            .map_err(|err| {
                error!(
                    "{}: channel_create(): Unable to read label from guest memory: {:?}",
                    self.pretty_name, err
                );
                OakStatus::ErrInvalidArgs
            })?;
        let label = Label::deserialize(&label_bytes).ok_or_else(|| {
            error!(
                "{}: channel_create: could not deserialize label",
                self.pretty_name
            );
            OakStatus::ErrInvalidArgs
        })?;

        let (write_handle, read_handle) = self.runtime.channel_create(&label)?;

        self.get_memory()
            .set_value(write_addr, write_handle as i64)
            .map_err(|err| {
                error!(
                    "{}: channel_create(): Unable to write writer handle into guest memory: {:?}",
                    self.pretty_name, err
                );
                OakStatus::ErrInvalidArgs
            })?;

        self.get_memory()
            .set_value(read_addr, read_handle as i64)
            .map_err(|err| {
                error!(
                    "{}: channel_create(): Unable to write reader handle into guest memory: {:?}",
                    self.pretty_name, err
                );
                OakStatus::ErrInvalidArgs
            })
    }

    /// Corresponds to the host ABI function [`channel_write`](https://github.com/project-oak/oak/blob/main/docs/abi.md#channel_write).
    fn channel_write(
        &self,
        writer_handle: oak_abi::Handle,
        source: AbiPointer,
        source_length: AbiPointerOffset,
        handles: AbiPointer,
        handles_count: AbiPointerOffset,
    ) -> Result<(), OakStatus> {
        trace!(
            "{}: channel_write({}, {}, {}, {}, {})",
            self.pretty_name,
            writer_handle,
            source,
            source_length,
            handles,
            handles_count
        );

        let data = self
            .get_memory()
            .get(source, source_length as usize)
            .map_err(|err| {
                error!(
                    "{}: channel_write(): Unable to read message data from guest memory: {:?}",
                    self.pretty_name, err
                );
                OakStatus::ErrInvalidArgs
            })?;

        let raw_handles = self
            .get_memory()
            .get(handles, handles_count as usize * 8)
            .map_err(|err| {
                error!(
                    "{}: channel_write(): Unable to read handles from guest memory: {:?}",
                    self.pretty_name, err
                );
                OakStatus::ErrInvalidArgs
            })?;

        let handles: Vec<u64> = raw_handles
            .chunks(8)
            .map(|bytes| LittleEndian::read_u64(bytes))
            .collect();
        let msg = NodeMessage { data, handles };

        self.runtime.channel_write(writer_handle, msg)?;

        Ok(())
    }

    /// Corresponds to the host ABI function [`channel_read`](https://github.com/project-oak/oak/blob/main/docs/abi.md#channel_read).
    #[allow(clippy::too_many_arguments)]
    fn channel_read(
        &mut self,
        reader_handle: oak_abi::Handle,

        dest: AbiPointer,
        dest_capacity: AbiPointerOffset,
        actual_length_addr: AbiPointer,

        handles_dest: AbiPointer,
        handles_capacity: AbiPointerOffset,
        actual_handle_count_addr: AbiPointer,
    ) -> Result<(), OakStatus> {
        trace!(
            "{}: channel_read({}, {}, {}, {}, {}, {}, {})",
            self.pretty_name,
            reader_handle,
            dest,
            dest_capacity,
            actual_length_addr,
            handles_dest,
            handles_capacity,
            actual_handle_count_addr
        );

        self.validate_ptr(dest, dest_capacity)?;
        self.validate_ptr(handles_dest, handles_capacity * 8)?;

        let msg = self.runtime.channel_try_read_message(
            reader_handle,
            dest_capacity as usize,
            handles_capacity as usize,
        )?;

        let (actual_length, actual_handle_count) = match &msg {
            None => (0, 0),
            Some(NodeReadStatus::Success(msg)) => (msg.data.len(), msg.handles.len()),
            Some(NodeReadStatus::NeedsCapacity(a, b)) => (*a, *b),
        };

        let raw_writer = &mut [0; 4];
        LittleEndian::write_u32(raw_writer, actual_length as u32);
        self.get_memory()
            .set(actual_length_addr, raw_writer)
            .map_err(|err| {
                error!(
                    "{}: channel_read(): Unable to write actual length into guest memory: {:?}",
                    self.pretty_name, err
                );
                OakStatus::ErrInvalidArgs
            })?;

        let raw_writer = &mut [0; 4];
        LittleEndian::write_u32(raw_writer, actual_handle_count as u32);
        self.get_memory()
            .set(actual_handle_count_addr, raw_writer)
            .map_err(|err| {
                error!(
                    "{}: channel_read(): Unable to write actual handle count into guest memory: {:?}",
                    self.pretty_name, err
                );
                OakStatus::ErrInvalidArgs
            })?;

        match msg {
            Some(NodeReadStatus::Success(msg)) => {
                self.get_memory().set(dest, &msg.data).map_err(|err| {
                    error!(
                        "{}: channel_read(): Unable to write destination buffer into guest memory: {:?}",
                        self.pretty_name, err
                    );
                    OakStatus::ErrInvalidArgs
                })?;

                let mut raw_writer: Vec<u8> = vec![0; actual_handle_count * 8];

                for (i, handle) in msg.handles.iter().enumerate() {
                    LittleEndian::write_u64(&mut raw_writer[i * 8..(i + 1) * 8], *handle);
                }

                self.get_memory()
                    .set(handles_dest, &raw_writer)
                    .map_err(|err| {
                        error!(
                            "{}: channel_read(): Unable to write destination buffer into guest memory: {:?}",
                            self.pretty_name, err
                        );
                        OakStatus::ErrInvalidArgs
                    })
            }
            None => Err(OakStatus::ErrChannelEmpty),
            Some(NodeReadStatus::NeedsCapacity(x, _)) => {
                if x > dest_capacity as usize {
                    Err(OakStatus::ErrBufferTooSmall)
                } else {
                    Err(OakStatus::ErrHandleSpaceTooSmall)
                }
            }
        }
    }

    /// Corresponds to the host ABI function [`wait_on_channels`](https://github.com/project-oak/oak/blob/main/docs/abi.md#wait_on_channels).
    ///
    /// May return the following error statuses:
    /// - `Err(OakStatus::ErrTerminated)`: if [`Runtime`] is terminating. In this case, read
    ///   statuses in `status_buff` do not reflect the actual read statuses.
    /// - `Err(OakStatus::ErrInvalidArgs)`: if cannot parse `status_buff` into channel handles.
    ///
    /// [`Runtime`]: crate::Runtime
    fn wait_on_channels(
        &mut self,
        status_buff: AbiPointer,
        handles_count: AbiPointerOffset,
    ) -> Result<(), OakStatus> {
        trace!(
            "{}: wait_on_channels({}, {})",
            self.pretty_name,
            status_buff,
            handles_count
        );

        let handles_raw: Vec<u8> = self
            .get_memory()
            .get(
                status_buff,
                handles_count as usize * oak_abi::SPACE_BYTES_PER_HANDLE,
            )
            .map_err(|err| {
                error!(
                    "{}: wait_on_channels(): Unable to read handles from guest memory: {:?}",
                    self.pretty_name, err
                );
                OakStatus::ErrInvalidArgs
            })?;
        let handles: Vec<oak_abi::Handle> = handles_raw
            .chunks(9)
            .map(|bytes| LittleEndian::read_u64(bytes))
            .collect();

        let statuses = self.runtime.wait_on_channels(&handles)?;
        for (i, status) in statuses.iter().enumerate() {
            self.get_memory()
                .set_value(status_buff + 8 + (i as u32 * 9), *status as u8)
                .map_err(|err| {
                    error!(
                        "{}: wait_on_channels(): Unable to set status[{}] to {:?}: {:?}",
                        self.pretty_name, i, status, err
                    );
                    OakStatus::ErrInvalidArgs
                })?;
        }

        Ok(())
    }
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

impl wasmi::Externals for WasmInterface {
    /// Invocation of a host function specified by registered index.  Acts as a wrapper for
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
            NODE_CREATE => map_host_errors(self.node_create(
                args.nth_checked(0)?,
                args.nth_checked(1)?,
                args.nth_checked(2)?,
                args.nth_checked(3)?,
                args.nth_checked(4)?,
            )),
            RANDOM_GET => {
                map_host_errors(self.random_get(args.nth_checked(0)?, args.nth_checked(1)?))
            }
            CHANNEL_CLOSE => map_host_errors(self.channel_close(args.nth_checked(0)?)),
            CHANNEL_CREATE => map_host_errors(self.channel_create(
                args.nth_checked(0)?,
                args.nth_checked(1)?,
                args.nth_checked(2)?,
                args.nth_checked(3)?,
            )),
            CHANNEL_WRITE => map_host_errors(self.channel_write(
                args.nth_checked(0)?,
                args.nth_checked(1)?,
                args.nth_checked(2)?,
                args.nth_checked(3)?,
                args.nth_checked(4)?,
            )),
            CHANNEL_READ => map_host_errors(self.channel_read(
                args.nth_checked(0)?,
                args.nth_checked(1)?,
                args.nth_checked(2)?,
                args.nth_checked(3)?,
                args.nth_checked(4)?,
                args.nth_checked(5)?,
                args.nth_checked(6)?,
            )),
            WAIT_ON_CHANNELS => {
                map_host_errors(self.wait_on_channels(args.nth_checked(0)?, args.nth_checked(1)?))
            }
            WASI_STUB => panic!("Attempt to invoke unimplemented WASI function"),
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
        oak_resolve_func(field_name, signature)
    }
}

/// A resolver function, mapping Oak host function names to an index and a type signature.
fn oak_resolve_func(
    field_name: &str,
    signature: &wasmi::Signature,
) -> Result<wasmi::FuncRef, wasmi::Error> {
    // The types in the signatures correspond to the parameters from
    // /oak/server/rust/oak_abi/src/lib.rs
    let (index, sig) = match field_name {
        "node_create" => (
            NODE_CREATE,
            wasmi::Signature::new(
                &[
                    ABI_USIZE,      // config_buf
                    ABI_USIZE,      // config_len
                    ABI_USIZE,      // label_buf
                    ABI_USIZE,      // label_len
                    ValueType::I64, // handle
                ][..],
                Some(ValueType::I32),
            ),
        ),
        "random_get" => (
            RANDOM_GET,
            wasmi::Signature::new(
                &[
                    ABI_USIZE, // buf
                    ABI_USIZE, // len
                ][..],
                Some(ValueType::I32),
            ),
        ),
        "channel_close" => (
            CHANNEL_CLOSE,
            wasmi::Signature::new(
                &[
                    ValueType::I64, // handle
                ][..],
                Some(ValueType::I32),
            ),
        ),
        "channel_create" => (
            CHANNEL_CREATE,
            wasmi::Signature::new(
                &[
                    ABI_USIZE, // write handle (out)
                    ABI_USIZE, // read handle (out)
                    ABI_USIZE, // label_buf
                    ABI_USIZE, // label_len
                ][..],
                Some(ValueType::I32),
            ),
        ),
        "channel_write" => (
            CHANNEL_WRITE,
            wasmi::Signature::new(
                &[
                    ValueType::I64, // handle
                    ABI_USIZE,      // buf
                    ABI_USIZE,      // size
                    ABI_USIZE,      // handle_buf
                    ValueType::I32, // handle_count
                ][..],
                Some(ValueType::I32),
            ),
        ),
        "channel_read" => (
            CHANNEL_READ,
            wasmi::Signature::new(
                &[
                    ValueType::I64, // handle
                    ABI_USIZE,      // buf
                    ABI_USIZE,      // size
                    ABI_USIZE,      // actual_size (out)
                    ABI_USIZE,      // handle_buf
                    ValueType::I32, // handle_count
                    ABI_USIZE,      // actual_handle_count (out)
                ][..],
                Some(ValueType::I32),
            ),
        ),
        "wait_on_channels" => (
            WAIT_ON_CHANNELS,
            wasmi::Signature::new(
                &[
                    ABI_USIZE,      // buf
                    ValueType::I32, // count
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
            "Export `{}` doesnt match expected type {:?}",
            field_name, signature
        )));
    }

    Ok(wasmi::FuncInstance::alloc_host(sig, index))
}

/// Stub version of `WasmInterface`, to allow checks of entrypoint signatures
/// and host function linking to be validated, without needing to construct
/// a full `WasmInterface` object.
struct WasmInterfaceStub;

impl wasmi::ModuleImportResolver for WasmInterfaceStub {
    /// Provide exactly the same set of host functions and signatures
    /// as the full [`WasmInterface`] does, so that Oak Wasm modules
    /// can be validated.
    fn resolve_func(
        &self,
        field_name: &str,
        signature: &wasmi::Signature,
    ) -> Result<wasmi::FuncRef, wasmi::Error> {
        oak_resolve_func(field_name, signature)
    }
}

/// Stub implementation of WASI exported functions, to allow partially-ported
/// applications that have references to WASI functions to be loaded. Note
/// that if the the application actually tries to *use* the WASI functions
/// at runtime, a panic will be triggered.
// TODO(#817): remove WASI stubs
struct WasiStub;

impl wasmi::ModuleImportResolver for WasiStub {
    fn resolve_func(
        &self,
        field_name: &str,
        signature: &wasmi::Signature,
    ) -> Result<wasmi::FuncRef, wasmi::Error> {
        let (index, sig) = match field_name {
            "proc_exit" => (
                WASI_STUB,
                wasmi::Signature::new(&[ValueType::I32][..], None),
            ),
            "fd_write" => (
                WASI_STUB,
                wasmi::Signature::new(
                    &[
                        ValueType::I32,
                        ValueType::I32,
                        ValueType::I32,
                        ValueType::I32,
                    ][..],
                    Some(ValueType::I32),
                ),
            ),
            "fd_seek" => (
                WASI_STUB,
                wasmi::Signature::new(
                    &[
                        ValueType::I32,
                        ValueType::I64,
                        ValueType::I32,
                        ValueType::I32,
                    ][..],
                    Some(ValueType::I32),
                ),
            ),
            "fd_close" => (
                WASI_STUB,
                wasmi::Signature::new(&[ValueType::I32][..], Some(ValueType::I32)),
            ),
            "environ_sizes_get" => (
                WASI_STUB,
                wasmi::Signature::new(&[ValueType::I32, ValueType::I32][..], Some(ValueType::I32)),
            ),
            "environ_get" => (
                WASI_STUB,
                wasmi::Signature::new(&[ValueType::I32, ValueType::I32][..], Some(ValueType::I32)),
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
                "Export `{}` doesnt match expected type {:?}",
                field_name, signature
            )));
        }

        Ok(wasmi::FuncInstance::alloc_host(sig, index))
    }
}

fn validate_entrypoint(module: &wasmi::Module, entrypoint: &str) -> Result<(), OakStatus> {
    let abi_stub = WasmInterfaceStub;
    let wasi_stub = WasiStub;
    let instance = wasmi::ModuleInstance::new(
        &module,
        &wasmi::ImportsBuilder::new()
            .with_resolver("oak", &abi_stub)
            .with_resolver("wasi_snapshot_preview1", &wasi_stub),
    )
    .expect("failed to instantiate wasm module")
    .assert_no_start();

    let expected_signature = wasmi::Signature::new(&[ValueType::I64][..], None);

    let export = instance.export_by_name(&entrypoint).ok_or_else(|| {
        warn!("entrypoint '{}' export not found", entrypoint);
        OakStatus::ErrInvalidArgs
    })?;

    let export_func = export.as_func().ok_or_else(|| {
        warn!("entrypoint '{}' export is not a function", entrypoint);
        OakStatus::ErrInvalidArgs
    })?;

    let export_func_signature = export_func.signature();
    if export_func_signature == &expected_signature {
        info!("entrypoint '{}' export validated", entrypoint);
        Ok(())
    } else {
        warn!(
            "entrypoint '{}' export has incorrect function signature: {:?}",
            entrypoint, export_func_signature
        );
        Err(OakStatus::ErrInvalidArgs)
    }
}

pub struct WasmNode {
    node_name: String,
    module: Arc<wasmi::Module>,
    entrypoint_name: String,
    node_privilege: NodePrivilege,
}

impl WasmNode {
    /// Creates a new [`WasmNode`] instance, but does not start it.
    /// May fail if the provided Wasm module is not valid.
    pub fn new(
        node_name: &str,
        application_configuration: &ApplicationConfiguration,
        node_configuration: WebAssemblyConfiguration,
    ) -> Result<Self, ConfigurationError> {
        let wasm_module_bytes = application_configuration
            .wasm_modules
            .get(&node_configuration.wasm_module_name)
            .ok_or(ConfigurationError::IncorrectWebAssemblyModuleName)?;
        let module = wasmi::Module::from_buffer(&wasm_module_bytes)
            .map_err(ConfigurationError::WasmiModuleInializationError)?;
        let entrypoint_name = node_configuration.wasm_entrypoint_name;
        validate_entrypoint(&module, &entrypoint_name).map_err(|err| {
            warn!("could not validate entrypoint: {:?}", err);
            ConfigurationError::IncorrectWebAssemblyModuleName
        })?;
        // We compute the node privilege once and for all at start and just store it, since it does
        // not change throughout the node execution.
        let node_privilege = wasm_node_privilege(&wasm_module_bytes);
        Ok(Self {
            node_name: node_name.to_string(),
            module: Arc::new(module),
            entrypoint_name,
            node_privilege,
        })
    }
}

/// Computes the [`NodePrivilege`] granted to a WebAssembly Node running the specified WebAssembly
/// module.
fn wasm_node_privilege(wasm_module_bytes: &[u8]) -> NodePrivilege {
    let mut hasher = sha2::Sha256::new();
    hasher.update(&wasm_module_bytes);
    let wasm_module_hash = hasher.finalize();
    debug!("Wasm module SHA-256 hash: {:x}", wasm_module_hash);
    NodePrivilege::new(
        hashset! { oak_abi::label::web_assembly_module_tag(&wasm_module_hash) },
        hashset! { oak_abi::label::web_assembly_module_tag(&wasm_module_hash) },
    )
}

impl super::Node for WasmNode {
    /// Runs this instance of a Wasm Node.
    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        debug!(
            "{}: running entrypoint '{}'",
            self.node_name, self.entrypoint_name
        );
        let wasi_stub = WasiStub;
        let mut abi = WasmInterface::new(&self.node_name, runtime);

        let instance = wasmi::ModuleInstance::new(
            &self.module,
            &wasmi::ImportsBuilder::new()
                .with_resolver("oak", &abi)
                .with_resolver("wasi_snapshot_preview1", &wasi_stub),
        )
        .expect("failed to instantiate wasm module")
        .assert_no_start();

        abi.memory = instance
            .export_by_name("memory")
            .unwrap()
            .as_memory()
            .cloned();

        let result = instance.invoke_export(
            &self.entrypoint_name,
            &[wasmi::RuntimeValue::I64(handle as i64)],
            &mut abi,
        );
        if let Err(err) = result {
            error!("Invocation of Wasm entrypoint failed: {:?}", err);
        }
        debug!(
            "{}: entrypoint '{}' completed",
            self.node_name, self.entrypoint_name
        );
    }

    fn get_privilege(&self) -> NodePrivilege {
        self.node_privilege.clone()
    }
}
