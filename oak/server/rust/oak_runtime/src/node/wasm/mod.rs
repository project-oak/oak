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

use std::{
    collections::HashMap,
    fmt::{self, Display, Formatter},
    string::String,
    sync::Arc,
    thread,
    thread::JoinHandle,
};

use log::{debug, error, info, warn};

use byteorder::{ByteOrder, LittleEndian};
use rand::RngCore;
use wasmi::ValueType;

use oak_abi::{label::Label, ChannelReadStatus, OakStatus};

use crate::{
    pretty_name_for_thread,
    runtime::{Handle, HandleDirection, ReadStatus, RuntimeProxy},
    Message,
};

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

type AbiPointer = u32;
type AbiPointerOffset = u32;

const ABI_U32: ValueType = ValueType::I32;
const ABI_U64: ValueType = ValueType::I64;
const ABI_USIZE: ValueType = ValueType::I32;

/// `WasmInterface` holds runtime values for a particular execution instance of Wasm. This includes
/// the host ABI function mapping between the Runtime and a Wasm instance, and the handle mapping
/// between the instance and the runtime `Handle`s.
///
/// Any handle from `readers` or `writers` is unique to all handles in both `readers` and
/// `writers`.
struct WasmInterface {
    /// A configuration and thread specific name for pretty printing.
    pretty_name: String,

    /// Reader channel mappings to unique u64 handles
    readers: HashMap<oak_abi::Handle, Handle>,
    /// Writer channel mappings to unique u64 handles
    writers: HashMap<oak_abi::Handle, Handle>,

    /// A reference to the memory used by the `wasmi` interpreter. Host ABI functions using Wasm
    /// relative addresses will perform reads/writes against this reference.
    memory: Option<wasmi::MemoryRef>,

    runtime: RuntimeProxy,
}

impl WasmInterface {
    /// Generate a randomized handle. Handles are random to prevent accidental dependency on
    /// particular values or sequence. See https://github.com/project-oak/oak/pull/347
    fn allocate_new_handle(
        &mut self,
        channel: Handle,
        direction: HandleDirection,
    ) -> oak_abi::Handle {
        loop {
            let handle = rand::thread_rng().next_u64();

            if self.readers.get(&handle).is_some() || self.writers.get(&handle).is_some() {
                continue;
            }

            if direction == HandleDirection::Read {
                self.readers.insert(handle, channel);
            } else {
                self.writers.insert(handle, channel);
            }

            return handle;
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

    /// Creates a new `WasmInterface` structure.
    pub fn new(
        pretty_name: String,
        runtime: RuntimeProxy,
        initial_reader: Handle,
    ) -> (WasmInterface, oak_abi::Handle) {
        let mut interface = WasmInterface {
            pretty_name,
            readers: HashMap::new(),
            writers: HashMap::new(),
            memory: None,
            runtime,
        };
        let handle = interface.allocate_new_handle(initial_reader, HandleDirection::Read);
        (interface, handle)
    }

    /// Corresponds to the host ABI function [`node_create: (usize, usize, usize, usize,
    /// u64) -> u32`](oak_abi::node_create).
    #[allow(clippy::too_many_arguments)]
    fn node_create(
        &self,
        name_ptr: AbiPointer,
        name_length: AbiPointerOffset,
        entrypoint_ptr: AbiPointer,
        entrypoint_length: AbiPointerOffset,
        label_ptr: AbiPointer,
        label_length: AbiPointerOffset,
        initial_handle: oak_abi::Handle,
    ) -> Result<(), OakStatus> {
        debug!(
            "{}: node_create({}, {}, {}, {}, {})",
            self.pretty_name,
            name_ptr,
            name_length,
            entrypoint_ptr,
            entrypoint_length,
            initial_handle
        );

        if self.runtime.is_terminating() {
            debug!("{}: node_create() returning terminated", self.pretty_name);
            return Err(OakStatus::ErrTerminated);
        }

        let config_name_bytes = self
            .get_memory()
            .get(name_ptr, name_length as usize)
            .map_err(|err| {
                error!(
                    "{}: node_create(): Unable to read name from guest memory: {:?}",
                    self.pretty_name, err
                );
                OakStatus::ErrInvalidArgs
            })?;
        let config_name = String::from_utf8(config_name_bytes).map_err(|err| {
            error!(
                "{}: node_create(): Unable to parse config_name: {:?}",
                self.pretty_name, err
            );
            OakStatus::ErrInvalidArgs
        })?;

        let entrypoint_bytes = self
            .get_memory()
            .get(entrypoint_ptr, entrypoint_length as usize)
            .map_err(|err| {
                error!(
                    "{}: node_create(): Unable to read entrypoint from guest memory: {:?}",
                    self.pretty_name, err
                );
                OakStatus::ErrInvalidArgs
            })?;
        let entrypoint = String::from_utf8(entrypoint_bytes).map_err(|err| {
            error!(
                "{}: node_create(): Unable to parse entrypoint: {:?}",
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

        debug!(
            "{}: node_create('{}', '{}', {:?})",
            self.pretty_name, config_name, entrypoint, label
        );
        let channel_ref = self.readers.get(&initial_handle).ok_or(()).map_err(|_| {
            error!(
                "{}: node_create(..., {}): Invalid handle",
                self.pretty_name, initial_handle
            );
            OakStatus::ErrBadHandle
        })?;

        self.runtime
            .clone()
            .node_create(&config_name, &entrypoint, &label, channel_ref.clone())
            .map_err(|_| {
                error!(
                    "{}: node_create(): Config \"{}\" entrypoint \"{}\" not found",
                    self.pretty_name, config_name, entrypoint
                );
                OakStatus::ErrInvalidArgs
            })
    }

    /// Corresponds to the host ABI function [`channel_create: (usize, usize) ->
    /// u32`](oak_abi::channel_create).
    fn channel_create(
        &mut self,
        write_addr: AbiPointer,
        read_addr: AbiPointer,
    ) -> Result<(), OakStatus> {
        debug!(
            "{}: channel_create({}, {})",
            self.pretty_name, write_addr, read_addr
        );

        if self.runtime.is_terminating() {
            debug!("{} returning terminated", self.pretty_name);
            return Err(OakStatus::ErrTerminated);
        }

        let (writer, reader) = self
            .runtime
            // TODO(#630): Let caller provide this label via the Wasm ABI.
            .channel_create(&Label::public_trusted());

        self.validate_ptr(write_addr, 8)?;
        self.validate_ptr(read_addr, 8)?;

        let write_handle = self.allocate_new_handle(writer, HandleDirection::Write);
        let read_handle = self.allocate_new_handle(reader, HandleDirection::Read);
        debug!(
            "{}: channel_create() -> ({}, {})",
            self.pretty_name, write_handle, read_handle
        );

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

    /// Corresponds to the host ABI function [`channel_write: (u64, usize, usize, usize, u32) ->
    /// u32`](oak_abi::channel_write).
    fn channel_write(
        &self,
        writer_handle: oak_abi::Handle,
        source: AbiPointer,
        source_length: AbiPointerOffset,
        handles: AbiPointer,
        handles_count: AbiPointerOffset,
    ) -> Result<(), OakStatus> {
        debug!(
            "{}: channel_write({}, {}, {}, {}, {})",
            self.pretty_name, writer_handle, source, source_length, handles, handles_count
        );

        let writer = self.writers.get(&writer_handle).ok_or(()).map_err(|_| {
            error!(
                "{}: channel_write({},...): No such handle",
                self.pretty_name, writer_handle
            );
            OakStatus::ErrBadHandle
        })?;

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

        let channels: Result<Vec<Handle>, _> = handles
            .iter()
            .map(|handle| match self.writers.get(handle) {
                Some(channel) => Ok(*channel),
                None => match self.readers.get(handle) {
                    Some(channel) => Ok(*channel),
                    None => {
                        error!(
                            "{}: channel_write(): Can't find handle {} to send",
                            self.pretty_name, handle
                        );
                        Err(OakStatus::ErrBadHandle)
                    }
                },
            })
            .collect();

        let msg = Message {
            data,
            channels: channels?,
        };

        self.runtime.channel_write(*writer, msg)?;

        Ok(())
    }

    /// Corresponds to the host ABI function [`channel_read: (u64, usize, usize, usize, usize, u32,
    /// usize) -> u32`](oak_abi::channel_read).
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
        debug!(
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

        let reader = self.readers.get(&reader_handle).ok_or(()).map_err(|_| {
            error!(
                "{}: channel_read(): No such handle {}",
                self.pretty_name, reader_handle
            );
            OakStatus::ErrBadHandle
        })?;

        self.validate_ptr(dest, dest_capacity)?;
        self.validate_ptr(handles_dest, handles_capacity * 8)?;

        let msg = self.runtime.channel_try_read_message(
            *reader,
            dest_capacity as usize,
            handles_capacity as usize,
        )?;

        let (actual_length, actual_handle_count) = match &msg {
            None => (0, 0),
            Some(ReadStatus::Success(msg)) => (msg.data.len(), msg.channels.len()),
            Some(ReadStatus::NeedsCapacity(a, b)) => (*a, *b),
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
            Some(ReadStatus::Success(msg)) => {
                self.get_memory().set(dest, &msg.data).map_err(|err| {
                    error!(
                        "{}: channel_read(): Unable to write destination buffer into guest memory: {:?}",
                        self.pretty_name, err
                    );
                    OakStatus::ErrInvalidArgs
                })?;

                let mut raw_writer: Vec<u8> = vec![0; actual_handle_count * 8];

                for (i, chan) in msg.channels.iter().enumerate() {
                    let handle =
                        self.allocate_new_handle(*chan, self.runtime.channel_get_direction(*chan)?);
                    LittleEndian::write_u64(&mut raw_writer[i * 8..(i + 1) * 8], handle);
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
            Some(ReadStatus::NeedsCapacity(x, _)) => {
                if x > dest_capacity as usize {
                    Err(OakStatus::ErrBufferTooSmall)
                } else {
                    Err(OakStatus::ErrHandleSpaceTooSmall)
                }
            }
        }
    }

    /// Corresponds to the host ABI function [`random_get: (usize, usize) ->
    /// u32`](oak_abi::random_get).
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

    /// Corresponds to the host ABI function [`channel_close: (u64) ->
    /// u32`](oak_abi::channel_close).
    fn channel_close(&mut self, handle: oak_abi::Handle) -> Result<(), OakStatus> {
        debug!("{}: channel_close({})", self.pretty_name, handle);

        if let Some(reference) = self.readers.get(&handle).cloned() {
            self.readers.remove(&handle);
            self.runtime
                .channel_close(reference)
                .expect("Wasm CHANNEL_CLOSE: Channel reference inconsistency!");
            Ok(())
        } else if let Some(reference) = self.writers.get(&handle).cloned() {
            self.writers.remove(&handle);
            self.runtime
                .channel_close(reference)
                .expect("Wasm CHANNEL_CLOSE: Channel reference inconsistency!");
            Ok(())
        } else {
            Err(OakStatus::ErrBadHandle)
        }
    }

    /// Corresponds to the host ABI function [`wait_on_channels: (usize, u32) ->
    /// u32`](oak_abi::wait_on_channels).
    fn wait_on_channels(
        &mut self,
        status_buff: AbiPointer,
        handles_count: AbiPointerOffset,
    ) -> Result<(), OakStatus> {
        debug!(
            "{}: wait_on_channels({}, {})",
            self.pretty_name, status_buff, handles_count
        );

        let handles_raw: Vec<u8> = self
            .get_memory()
            .get(status_buff, handles_count as usize * 9)
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

        // Accumulate both the valid channels and their original position.
        let mut all_statuses = vec![ChannelReadStatus::InvalidChannel; handles.len()];
        let mut valid_pos = Vec::new();
        let mut valid_channels = Vec::new();
        for (i, handle) in handles.into_iter().enumerate() {
            if let Some(channel) = self.readers.get(&handle).copied() {
                valid_pos.push(i);
                valid_channels.push(channel);
            }
        }
        let valid_statuses = self.runtime.wait_on_channels(&valid_channels)?;
        for i in 0..valid_channels.len() {
            all_statuses[valid_pos[i]] = valid_statuses[i];
        }

        for (i, valid_status) in all_statuses.iter().enumerate() {
            self.get_memory()
                .set_value(status_buff + 8 + (i as u32 * 9), *valid_status as u8)
                .map_err(|err| {
                    error!(
                        "{}: wait_on_channels(): Unable to set status[{}] to {:?}: {:?}",
                        self.pretty_name, i, valid_status, err
                    );
                    OakStatus::ErrInvalidArgs
                })?;
        }

        if all_statuses
            .iter()
            .all(|&s| s == ChannelReadStatus::InvalidChannel || s == ChannelReadStatus::Orphaned)
        {
            Err(OakStatus::ErrBadHandle)
        } else {
            Ok(())
        }
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
    ///   types that were specified when the host function was registered with `resolv_func`.
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
                args.nth_checked(5)?,
                args.nth_checked(6)?,
            )),
            RANDOM_GET => {
                map_host_errors(self.random_get(args.nth_checked(0)?, args.nth_checked(1)?))
            }
            CHANNEL_CLOSE => map_host_errors(self.channel_close(args.nth_checked(0)?)),
            CHANNEL_CREATE => {
                map_host_errors(self.channel_create(args.nth_checked(0)?, args.nth_checked(1)?))
            }
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
    /// A resolver function, mapping function names to an index and a type signature.
    fn resolve_func(
        &self,
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
                        ABI_USIZE, // config_buf
                        ABI_USIZE, // config_len
                        ABI_USIZE, // entrypoint_buf
                        ABI_USIZE, // entrypoint_len
                        ABI_USIZE, // label_buf
                        ABI_USIZE, // label_len
                        ABI_U64,   // handle
                    ][..],
                    Some(ABI_U32),
                ),
            ),
            "random_get" => (
                RANDOM_GET,
                wasmi::Signature::new(
                    &[
                        ABI_USIZE, // buf
                        ABI_USIZE, // len
                    ][..],
                    Some(ABI_U32),
                ),
            ),
            "channel_close" => (
                CHANNEL_CLOSE,
                wasmi::Signature::new(
                    &[
                        ABI_U64, // handle
                    ][..],
                    Some(ABI_U32),
                ),
            ),
            "channel_create" => (
                CHANNEL_CREATE,
                wasmi::Signature::new(
                    &[
                        ABI_USIZE, // write
                        ABI_USIZE, // read
                    ][..],
                    Some(ABI_U32),
                ),
            ),
            "channel_write" => (
                CHANNEL_WRITE,
                wasmi::Signature::new(
                    &[
                        ABI_U64,   // handle
                        ABI_USIZE, // buf
                        ABI_USIZE, // size
                        ABI_USIZE, // handle_buf
                        ABI_U32,   // handle_count
                    ][..],
                    Some(ABI_U32),
                ),
            ),
            "channel_read" => (
                CHANNEL_READ,
                wasmi::Signature::new(
                    &[
                        ABI_U64,   // handle
                        ABI_USIZE, // buf
                        ABI_USIZE, // size
                        ABI_USIZE, // actual_size
                        ABI_USIZE, // handle_buf
                        ABI_U32,   // handle_count
                        ABI_USIZE, // actual_handle_count
                    ][..],
                    Some(ABI_U32),
                ),
            ),
            "wait_on_channels" => (
                WAIT_ON_CHANNELS,
                wasmi::Signature::new(
                    &[
                        ABI_USIZE, // buf
                        ABI_U32,   // count
                    ][..],
                    Some(ABI_U32),
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
}

// Stub implementation of WASI exported functions, to allow partially-ported
// applications to be run.
// TODO(#817): remove WASI stubs
struct WasiStub;

impl wasmi::ModuleImportResolver for WasiStub {
    fn resolve_func(
        &self,
        field_name: &str,
        signature: &wasmi::Signature,
    ) -> Result<wasmi::FuncRef, wasmi::Error> {
        let (index, sig) = match field_name {
            "proc_exit" => (WASI_STUB, wasmi::Signature::new(&[ABI_U32][..], None)),
            "fd_write" => (
                WASI_STUB,
                wasmi::Signature::new(&[ABI_U32, ABI_U32, ABI_U32, ABI_U32][..], Some(ABI_U32)),
            ),
            "fd_seek" => (
                WASI_STUB,
                wasmi::Signature::new(&[ABI_U32, ABI_U64, ABI_U32, ABI_U32][..], Some(ABI_U32)),
            ),
            "fd_close" => (
                WASI_STUB,
                wasmi::Signature::new(&[ABI_U32][..], Some(ABI_U32)),
            ),
            "environ_sizes_get" => (
                WASI_STUB,
                wasmi::Signature::new(&[ABI_U32, ABI_U32][..], Some(ABI_U32)),
            ),
            "environ_get" => (
                WASI_STUB,
                wasmi::Signature::new(&[ABI_U32, ABI_U32][..], Some(ABI_U32)),
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

pub struct WasmNode {
    config_name: String,
    runtime: RuntimeProxy,
    module: Arc<wasmi::Module>,
    entrypoint: String,
    reader: Handle,
}

impl WasmNode {
    /// Creates a new [`WasmNode`] instance, but does not start it.
    pub fn new(
        config_name: &str,
        runtime: RuntimeProxy,
        module: Arc<wasmi::Module>,
        entrypoint: String,
        reader: Handle,
    ) -> Self {
        Self {
            config_name: config_name.to_string(),
            runtime,
            module,
            entrypoint,
            reader,
        }
    }

    fn validate_entrypoint(&self) -> Result<(), OakStatus> {
        let (abi, _) =
            WasmInterface::new(self.config_name.clone(), self.runtime.clone(), self.reader);
        let wasi_stub = WasiStub;
        let instance = wasmi::ModuleInstance::new(
            &self.module,
            &wasmi::ImportsBuilder::new()
                .with_resolver("oak", &abi)
                .with_resolver("wasi_snapshot_preview1", &wasi_stub),
        )
        .expect("failed to instantiate wasm module")
        .assert_no_start();

        let expected_signature = wasmi::Signature::new(&[ABI_U64][..], None);

        let export = instance.export_by_name(&self.entrypoint).ok_or_else(|| {
            warn!("entrypoint '{}' export not found", self.entrypoint);
            OakStatus::ErrInvalidArgs
        })?;

        let export_func = export.as_func().ok_or_else(|| {
            warn!("entrypoint '{}' export is not a function", self.entrypoint);
            OakStatus::ErrInvalidArgs
        })?;

        let export_func_signature = export_func.signature();
        if export_func_signature == &expected_signature {
            info!("entrypoint '{}' export validated", self.entrypoint);
            Ok(())
        } else {
            warn!(
                "entrypoint '{}' export has incorrect function signature: {:?}",
                self.entrypoint, export_func_signature
            );
            Err(OakStatus::ErrInvalidArgs)
        }
    }

    /// Main node worker thread.
    fn worker_thread(self) {
        let pretty_name = pretty_name_for_thread(&thread::current());
        let wasi_stub = WasiStub;
        let (mut abi, initial_handle) =
            WasmInterface::new(pretty_name, self.runtime.clone(), self.reader);

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

        instance
            .invoke_export(
                &self.entrypoint,
                &[wasmi::RuntimeValue::I64(initial_handle as i64)],
                &mut abi,
            )
            .expect("failed to execute export");

        self.runtime.exit_node();
    }
}

impl Display for WasmNode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "WasmNode({})", self.config_name)
    }
}

impl super::Node for WasmNode {
    /// Starts this instance of a Wasm Node.
    ///
    /// If the entry point is not found, returns `Err(OakStatus::ErrInvalidArgs)` immediately.
    fn start(self: Box<Self>) -> Result<JoinHandle<()>, OakStatus> {
        debug!(
            "Node::start(): discovering '{}' '{}'",
            self.config_name, self.entrypoint
        );

        // wasmi can't enumerate exports at creation, so we have to do it here per instance spawned
        // as the entrypoint could be anything. We do it before spawning the child thread so
        // that we can return an error code immediately if appropriate.
        self.validate_entrypoint()?;

        debug!(
            "Node::start(): starting '{}' '{}'",
            self.config_name, self.entrypoint
        );

        let thread_handle = thread::Builder::new()
            .name(self.to_string())
            .spawn(move || self.worker_thread())
            .expect("failed to spawn thread");
        Ok(thread_handle)
    }
}
