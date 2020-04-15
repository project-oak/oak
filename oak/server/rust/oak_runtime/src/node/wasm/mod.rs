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

use log::{debug, error};

use byteorder::{ByteOrder, LittleEndian};
use rand::RngCore;
use wasmi::ValueType;

use oak_abi::{ChannelReadStatus, OakStatus};

use crate::{
    pretty_name_for_thread,
    runtime::{Handle, HandleDirection, ReadStatus, RuntimeProxy},
    Message,
};

#[cfg(test)]
mod tests;

/// These number mappings are not exposed to the Wasm client, and are only used by `wasmi` to map
/// import names to host functions. See https://docs.rs/wasmi/0.6.2/wasmi/trait.Externals.html
///
/// - 0: node_create: (usize, usize, usize, usize, u64) -> u32
/// - 1: random_get: (usize, usize) -> u32
/// - 2: channel_close: (u64) -> u32
/// - 3: channel_create: (usize, usize) -> u32
/// - 4: channel_write: (u64, usize, usize, usize, u32) -> u32
/// - 5: channel_read: (u64, usize, usize, usize, usize, u32, usize) -> u32
/// - 6: wait_on_channels: (usize, u32) -> u32

const NODE_CREATE: usize = 0;
const RANDOM_GET: usize = 1;
const CHANNEL_CLOSE: usize = 2;
const CHANNEL_CREATE: usize = 3;
const CHANNEL_WRITE: usize = 4;
const CHANNEL_READ: usize = 5;
const WAIT_ON_CHANNELS: usize = 6;
// TODO(#817): remove this
const WASI_STUB: usize = 7;

type AbiHandle = u64;
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
    readers: HashMap<AbiHandle, Handle>,
    /// Writer channel mappings to unique u64 handles
    writers: HashMap<AbiHandle, Handle>,

    /// A reference to the memory used by the `wasmi` interpreter. Host ABI functions using Wasm
    /// relative addresses will perform reads/writes against this reference.
    memory: Option<wasmi::MemoryRef>,

    runtime: RuntimeProxy,
}

impl WasmInterface {
    /// Generate a randomized handle. Handles are random to prevent accidental dependency on
    /// particular values or sequence. See https://github.com/project-oak/oak/pull/347
    fn allocate_new_handle(&mut self, channel: Handle, direction: HandleDirection) -> AbiHandle {
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

    /// Make sure a given address range falls within the currently allocated range of memory.
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
    ) -> (WasmInterface, AbiHandle) {
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

    /// Corresponds to the host ABI function `node_create: (usize, usize, usize, usize, u64) ->
    /// u32`.
    fn node_create(
        &self,
        name_ptr: AbiPointer,
        name_length: AbiPointerOffset,
        entrypoint_ptr: AbiPointer,
        entrypoint_length: AbiPointerOffset,
        initial_handle: AbiHandle,
    ) -> Result<(), OakStatus> {
        let config_name = self
            .get_memory()
            .get(name_ptr, name_length as usize)
            .map_err(|err| {
                error!(
                    "node_create: Unable to read name from guest memory: {:?}",
                    err
                );
                OakStatus::ErrInvalidArgs
            })?;

        let config_name = String::from_utf8(config_name).map_err(|err| {
            error!("node_create: Unable to parse config_name: {:?}", err);
            OakStatus::ErrInvalidArgs
        })?;

        debug!(
            "{} node_create config_name is: {}",
            self.pretty_name, config_name
        );

        let entrypoint = self
            .get_memory()
            .get(entrypoint_ptr, entrypoint_length as usize)
            .map_err(|err| {
                error!(
                    "node_create: Unable to read entrypoint from guest memory: {:?}",
                    err
                );
                OakStatus::ErrInvalidArgs
            })?;

        let entrypoint = String::from_utf8(entrypoint).map_err(|err| {
            error!("node_create: Unable to parse entrypoint: {:?}", err);
            OakStatus::ErrInvalidArgs
        })?;

        debug!(
            "{} node_create entrypoint is: {}",
            self.pretty_name, entrypoint
        );

        let channel_ref = self.readers.get(&initial_handle).ok_or(()).map_err(|_| {
            error!("node_create: Invalid handle");
            OakStatus::ErrBadHandle
        })?;

        self.runtime
            .clone()
            .node_create(
                &config_name,
                &entrypoint,
                // TODO(#630): Let caller provide this label via the Wasm ABI.
                &oak_abi::label::Label::public_trusted(),
                channel_ref.clone(),
            )
            .map_err(|_| {
                error!(
                    "node_create: Config \"{}\" entrypoint \"{}\" not found",
                    config_name, entrypoint
                );
                OakStatus::ErrInvalidArgs
            })
    }

    /// Corresponds to the host ABI function `channel_create: (usize, usize) -> u32`.
    fn channel_create(
        &mut self,
        write_addr: AbiPointer,
        read_addr: AbiPointer,
    ) -> Result<(), OakStatus> {
        let (writer, reader) = self
            .runtime
            // TODO(#630): Let caller provide this label via the Wasm ABI.
            .channel_create(&oak_abi::label::Label::public_trusted());

        self.validate_ptr(write_addr, 8)?;
        self.validate_ptr(read_addr, 8)?;

        let write_handle = self.allocate_new_handle(writer, HandleDirection::Write);
        let read_handle = self.allocate_new_handle(reader, HandleDirection::Read);

        self.get_memory()
            .set_value(write_addr, write_handle as i64)
            .map_err(|err| {
                error!(
                    "channel_create: Unable to write writer handle into guest memory: {:?}",
                    err
                );
                OakStatus::ErrInvalidArgs
            })?;

        self.get_memory()
            .set_value(read_addr, read_handle as i64)
            .map_err(|err| {
                error!(
                    "channel_create: Unable to write reader handle into guest memory: {:?}",
                    err
                );
                OakStatus::ErrInvalidArgs
            })
    }

    /// Corresponds to the host ABI function `channel_write: (u64, usize, usize, usize, u32) ->
    /// u32`
    fn channel_write(
        &self,
        writer_handle: AbiHandle,
        source: AbiPointer,
        source_length: AbiPointerOffset,
        handles: AbiPointer,
        handles_count: AbiPointerOffset,
    ) -> Result<(), OakStatus> {
        let writer = self.writers.get(&writer_handle).ok_or(()).map_err(|_| {
            error!("channel_write: No such handle");
            OakStatus::ErrBadHandle
        })?;

        let data = self
            .get_memory()
            .get(source, source_length as usize)
            .map_err(|err| {
                error!(
                    "channel_write: Unable to read message data from guest memory: {:?}",
                    err
                );
                OakStatus::ErrInvalidArgs
            })?;

        let raw_handles = self
            .get_memory()
            .get(handles, handles_count as usize * 8)
            .map_err(|err| {
                error!(
                    "channel_write: Unable to read handles from guest memory: {:?}",
                    err
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
                        error!("channel_write: Can't find handle {} to send", handle);
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

    #[allow(clippy::too_many_arguments)]
    /// Corresponds to the host ABI function `channel_read: (u64, usize, usize, usize, usize, u32,
    /// usize) -> u32`
    fn channel_read(
        &mut self,
        reader_handle: AbiHandle,

        dest: AbiPointer,
        dest_capacity: AbiPointerOffset,
        actual_length_addr: AbiPointer,

        handles_dest: AbiPointer,
        handles_capcity: AbiPointerOffset,
        actual_handle_count_addr: AbiPointer,
    ) -> Result<(), OakStatus> {
        let reader = self.readers.get(&reader_handle).ok_or(()).map_err(|_| {
            error!("channel_read: No such handle");
            OakStatus::ErrBadHandle
        })?;

        self.validate_ptr(dest, dest_capacity)?;
        self.validate_ptr(handles_dest, handles_capcity * 8)?;

        let msg = self.runtime.channel_try_read_message(
            *reader,
            dest_capacity as usize,
            handles_capcity as usize,
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
                    "channel_read: Unable to write actual length into guest memory: {:?}",
                    err
                );
                OakStatus::ErrInvalidArgs
            })?;

        let raw_writer = &mut [0; 4];
        LittleEndian::write_u32(raw_writer, actual_handle_count as u32);
        self.get_memory()
            .set(actual_handle_count_addr, raw_writer)
            .map_err(|err| {
                error!(
                    "channel_read: Unable to write actual handle count into guest memory: {:?}",
                    err
                );
                OakStatus::ErrInvalidArgs
            })?;

        match msg {
            Some(ReadStatus::Success(msg)) => {
                self.get_memory().set(dest, &msg.data).map_err(|err| {
                    error!(
                        "channel_read: Unable to write destination buffer into guest memory: {:?}",
                        err
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
                        "channel_read: Unable to write destination buffer into guest memory: {:?}",
                        err
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

    /// Corresponds to the host ABI function `random_get: (usize, usize) -> u32`
    fn random_get(&self, dest: AbiPointer, dest_length: AbiPointerOffset) -> Result<(), OakStatus> {
        self.validate_ptr(dest, dest_length)?;

        let dest = dest as usize;
        let dest_length = dest_length as usize;

        self.get_memory().with_direct_access_mut(|memory| {
            rand::thread_rng().fill_bytes(&mut memory[dest..(dest + dest_length)]);
        });

        Ok(())
    }

    /// Corresponds to the host ABI function `wait_on_channels: (usize, u32) -> u32`
    fn wait_on_channels(
        &mut self,
        status_buff: AbiPointer,
        handles_count: AbiPointerOffset,
    ) -> Result<(), OakStatus> {
        let handles_raw: Vec<u8> = self
            .get_memory()
            .get(status_buff, handles_count as usize * 9)
            .map_err(|err| {
                error!(
                    "wait_on_channels: Unable to read handles from guest memory: {:?}",
                    err
                );
                OakStatus::ErrInvalidArgs
            })?;

        let channels: Vec<Option<_>> = handles_raw
            .chunks(9)
            .map(|bytes| {
                let handle = LittleEndian::read_u64(bytes);

                self.readers.get(&handle).copied()
            })
            .collect();

        let statuses = self.runtime.wait_on_channels(&channels)?;

        for (i, &status) in statuses.iter().enumerate() {
            self.get_memory()
                .set_value(status_buff + 8 + (i as u32 * 9), status as u8)
                .map_err(|err| {
                    error!(
                        "wait_on_channels: Unable to set status {} to {:?}: {:?}",
                        i, status, err
                    );
                    OakStatus::ErrInvalidArgs
                })?;
        }

        if statuses
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
/// `wasmi` specific result type `Result<Option<wasmi::RuntimeValue>, wasmi::Trap>`.
///
/// This maps`Result<(), OakStatus>` to `Ok(Some(<wasmi::RuntimeValue>))` where
/// - `Ok(())` to `OakStatus::Ok`
/// - `Err(x)` to x
fn map_host_errors(
    result: Result<(), OakStatus>,
) -> Result<Option<wasmi::RuntimeValue>, wasmi::Trap> {
    Ok(Some(wasmi::RuntimeValue::I32(result.map_or_else(
        |x: OakStatus| x as i32,
        |_| OakStatus::Ok as i32,
    ))))
}

impl wasmi::Externals for WasmInterface {
    /// This function maps a function index corresponding to one of the host ABI functions we
    /// export to the Wasm guest, and some passed arguments, to our native function. The arguments
    /// should be the correct types as `resolve_func` will have already informed the `wasmi`
    /// interpreter of the types of our functions. However, arguments are still checked via the
    /// `nth_checked` method, and values are checked our native methods.
    fn invoke_index(
        &mut self,
        index: usize,
        args: wasmi::RuntimeArgs,
    ) -> Result<Option<wasmi::RuntimeValue>, wasmi::Trap> {
        debug!("{} invoke_index: {} {:?}", self.pretty_name, index, args);

        match index {
            NODE_CREATE => {
                let name_ptr: u32 = args.nth_checked(0)?;
                let name_length: u32 = args.nth_checked(1)?;
                let entrypoint_ptr: u32 = args.nth_checked(2)?;
                let entrypoint_length: u32 = args.nth_checked(3)?;
                let initial_handle: u64 = args.nth_checked(4)?;

                debug!(
                    "{} node_create: {} {} {} {} {}",
                    self.pretty_name,
                    name_ptr,
                    name_length,
                    entrypoint_ptr,
                    entrypoint_length,
                    initial_handle
                );

                if self.runtime.is_terminating() {
                    debug!("{} returning terminated", self.pretty_name);
                    return Ok(Some(wasmi::RuntimeValue::I32(
                        OakStatus::ErrTerminated as i32,
                    )));
                }

                map_host_errors(self.node_create(
                    name_ptr,
                    name_length,
                    entrypoint_ptr,
                    entrypoint_length,
                    initial_handle,
                ))
            }

            RANDOM_GET => {
                let dest: u32 = args.nth_checked(0)?;
                let dest_length: u32 = args.nth_checked(1)?;

                debug!("{} random_get: {} {}", self.pretty_name, dest, dest_length);

                map_host_errors(self.random_get(dest, dest_length))
            }

            CHANNEL_CLOSE => {
                let channel_id: u64 = args.nth_checked(0)?;

                debug!("{} channel_close: {}", self.pretty_name, channel_id);

                let result = if let Some(reference) = self.readers.get(&channel_id).cloned() {
                    self.readers.remove(&channel_id);
                    self.runtime
                        .channel_close(reference)
                        .expect("Wasm CHANNEL_CLOSE: Channel reference inconsistency!");
                    OakStatus::Ok as i32
                } else if let Some(reference) = self.writers.get(&channel_id).cloned() {
                    self.writers.remove(&channel_id);
                    self.runtime
                        .channel_close(reference)
                        .expect("Wasm CHANNEL_CLOSE: Channel reference inconsistency!");
                    OakStatus::Ok as i32
                } else {
                    OakStatus::ErrBadHandle as i32
                };

                Ok(Some(wasmi::RuntimeValue::I32(result)))
            }

            CHANNEL_CREATE => {
                let write_addr: u32 = args.nth_checked(0)?;
                let read_addr: u32 = args.nth_checked(1)?;

                debug!(
                    "{} channel_create: {} {}",
                    self.pretty_name, write_addr, read_addr
                );

                if self.runtime.is_terminating() {
                    debug!("{} returning terminated", self.pretty_name);
                    return Ok(Some(wasmi::RuntimeValue::I32(
                        OakStatus::ErrTerminated as i32,
                    )));
                }

                map_host_errors(self.channel_create(write_addr, read_addr))
            }

            CHANNEL_WRITE => {
                let writer_handle: u64 = args.nth_checked(0)?;
                let source: u32 = args.nth_checked(1)?;
                let source_length: u32 = args.nth_checked(2)?;
                let handles: u32 = args.nth_checked(3)?;
                let handles_count: u32 = args.nth_checked(4)?;

                debug!(
                    "{} channel_write: {} {} {} {} {}",
                    self.pretty_name, writer_handle, source, source_length, handles, handles_count
                );

                map_host_errors(self.channel_write(
                    writer_handle,
                    source,
                    source_length,
                    handles,
                    handles_count,
                ))
            }

            CHANNEL_READ => {
                let reader_handle: u64 = args.nth_checked(0)?;

                let dest: u32 = args.nth_checked(1)?;
                let dest_capacity: u32 = args.nth_checked(2)?;
                let actual_length: u32 = args.nth_checked(3)?;

                let handles: u32 = args.nth_checked(4)?;
                let handles_capcity: u32 = args.nth_checked(5)?;
                let actual_handle_count: u32 = args.nth_checked(6)?;

                debug!(
                    "{} channel_read: {} {} {} {} {} {} {}",
                    self.pretty_name,
                    reader_handle,
                    dest,
                    dest_capacity,
                    actual_length,
                    handles,
                    handles_capcity,
                    actual_handle_count
                );

                map_host_errors(self.channel_read(
                    reader_handle,
                    dest,
                    dest_capacity,
                    actual_length,
                    handles,
                    handles_capcity,
                    actual_handle_count,
                ))
            }

            WAIT_ON_CHANNELS => {
                let status_buff: u32 = args.nth_checked(0)?;
                let handles_count: u32 = args.nth_checked(1)?;

                debug!(
                    "{} wait_on_channels: {} {}",
                    self.pretty_name, status_buff, handles_count
                );

                map_host_errors(self.wait_on_channels(status_buff, handles_count))
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
        let (index, sig) = match field_name {
            //
            // - 0: node_create: (usize, usize, usize, usize, u64) -> u32
            "node_create" => (
                NODE_CREATE,
                wasmi::Signature::new(
                    &[ABI_USIZE, ABI_USIZE, ABI_USIZE, ABI_USIZE, ABI_U64][..],
                    Some(ABI_U32),
                ),
            ),
            //
            // - 1: random_get: (usize, usize) -> u32
            "random_get" => (
                RANDOM_GET,
                wasmi::Signature::new(&[ABI_USIZE, ABI_USIZE][..], Some(ABI_U32)),
            ),
            //
            // - 2: channel_close: (u64) -> u32
            "channel_close" => (
                CHANNEL_CLOSE,
                wasmi::Signature::new(&[ABI_U64][..], Some(ABI_U32)),
            ),
            //
            // - 3: channel_create: (usize, usize) -> u32
            "channel_create" => (
                CHANNEL_CREATE,
                wasmi::Signature::new(&[ABI_USIZE, ABI_USIZE][..], Some(ABI_U32)),
            ),
            //
            // - 4: channel_write: (u64, usize, usize, usize, u32) -> u32
            "channel_write" => (
                CHANNEL_WRITE,
                wasmi::Signature::new(
                    &[ABI_U64, ABI_USIZE, ABI_USIZE, ABI_USIZE, ABI_U32][..],
                    Some(ABI_U32),
                ),
            ),
            //
            // - 5: channel_read: (u64, usize, usize, usize, usize, u32, usize) -> u32
            "channel_read" => (
                CHANNEL_READ,
                wasmi::Signature::new(
                    &[
                        ABI_U64, ABI_USIZE, ABI_USIZE, ABI_USIZE, ABI_USIZE, ABI_U32, ABI_USIZE,
                    ][..],
                    Some(ABI_U32),
                ),
            ),
            //
            // - 6: wait_on_channels: (usize, u32) -> u32
            "wait_on_channels" => (
                WAIT_ON_CHANNELS,
                wasmi::Signature::new(&[ABI_USIZE, ABI_U32][..], Some(ABI_U32)),
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
    thread_handle: Option<JoinHandle<()>>,
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
            thread_handle: None,
        }
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
    fn start(&mut self) -> Result<(), OakStatus> {
        debug!(
            "new_instance: discovering {} {}",
            self.config_name, self.entrypoint
        );

        // wasmi can't enumerate exports at creation, so we have to do it here per instance spawned
        // as the entrypoint could be anything. We do it before spawning the child thread so
        // that we can return an error code immediately if appropriate.
        {
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

            let entrypoint_sig = wasmi::Signature::new(&[ABI_U64][..], None);

            if instance
                .export_by_name(&self.entrypoint)
                .and_then(|e| e.as_func().map(|f| f.signature() != &entrypoint_sig))
                .unwrap_or(true)
            {
                return Err(OakStatus::ErrInvalidArgs);
            }
        }

        debug!(
            "new_instance: starting {} {}",
            self.config_name, self.entrypoint
        );

        // Clone or copy all the captured values and move them into the closure, for simplicity.
        let reader = self.reader;
        let runtime = self.runtime.clone();
        let module = self.module.clone();
        let entrypoint = self.entrypoint.clone();
        let thread_handle = thread::Builder::new()
            .name(self.to_string())
            .spawn(move || {
                let pretty_name = pretty_name_for_thread(&thread::current());
                let wasi_stub = WasiStub;
                let (mut abi, initial_handle) =
                    WasmInterface::new(pretty_name, runtime.clone(), reader);

                let instance = wasmi::ModuleInstance::new(
                    &module,
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
                        &entrypoint,
                        &[wasmi::RuntimeValue::I64(initial_handle as i64)],
                        &mut abi,
                    )
                    .expect("failed to execute export");

                runtime.exit_node();
            })
            .expect("failed to spawn thread");
        self.thread_handle = Some(thread_handle);
        Ok(())
    }
    fn stop(&mut self) {
        if let Some(join_handle) = self.thread_handle.take() {
            if let Err(err) = join_handle.join() {
                error!("error while stopping Wasm node: {:?}", err);
            }
        }
    }
}
