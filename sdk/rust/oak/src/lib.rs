//
// Copyright 2018 The Project Oak Authors
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

use byteorder::{ReadBytesExt, WriteBytesExt};

use log::{debug, error};
use protobuf::ProtobufEnum;
use serde::{Deserialize, Serialize};

// Re-export ABI constants that are also visible as part of the SDK API.
pub use oak_abi::{ChannelReadStatus, OakStatus};

pub mod grpc;
pub mod io;
pub mod proto;
pub mod rand;
pub mod storage;
#[cfg(test)]
mod tests;

#[cfg(test)]
use assert_matches::assert_matches;
#[cfg(test)]
use serial_test_derive::serial;

/// Handle used to identify read or write channel halves.
///
/// These handles are used for all host function calls.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Handle {
    id: u64,
}

/// Serialize a `Handle` as the invalid handle value.
impl serde::Serialize for Handle {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_u64(oak_abi::INVALID_HANDLE)
    }
}

struct HandleVisitor;

/// Deserialize a `Handle` as the invalid handle value. Most likely, it will have been serialized to
/// an invalid handle in the first place anyways, but we are being extra cautions and even if the
/// serialized value was modified, we make sure that the resulting `Handle` is invalid.
impl<'de> serde::de::Visitor<'de> for HandleVisitor {
    type Value = Handle;
    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a handle type")
    }

    fn visit_u64<E>(self, _v: u64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Handle::invalid())
    }
}

impl<'de> serde::Deserialize<'de> for Handle {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_u64(HandleVisitor)
    }
}

impl Handle {
    /// When using the Oak SDK, this method should not need to be called directly
    /// as `Handles` are directly provided via functions such as `channel_create`.
    pub fn from_raw(id: u64) -> Handle {
        Handle { id }
    }

    /// Check this handle is valid.
    pub fn is_valid(self) -> bool {
        self.id != oak_abi::INVALID_HANDLE
    }

    /// Returns an intentionally invalid handle.
    pub fn invalid() -> Handle {
        Handle {
            id: oak_abi::INVALID_HANDLE,
        }
    }

    /// Pack a slice of `Handles` into the Wasm host ABI format.
    fn pack(handles: &[Handle]) -> Vec<u8> {
        let mut packed = Vec::with_capacity(handles.len() * 8);
        for handle in handles {
            packed
                .write_u64::<byteorder::LittleEndian>(handle.id)
                .unwrap();
        }
        packed
    }

    /// Unpack a slice of Handles from the Wasm host ABI format.
    fn unpack(bytes: &[u8], handle_count: u32, handles: &mut Vec<Handle>) {
        handles.clear();
        let mut reader = std::io::Cursor::new(bytes);
        for _ in 0..handle_count {
            handles.push(Handle {
                id: reader.read_u64::<byteorder::LittleEndian>().unwrap(),
            });
        }
    }
}

/// Wrapper for a handle to the read half of a channel.
///
/// For use when the underlying [`Handle`] is known to be for a receive half.
#[derive(Debug, Copy, Clone, PartialEq, Serialize, Deserialize)]
pub struct ReadHandle {
    pub handle: Handle,
}

/// Wrapper for a handle to the send half of a channel.
///
/// For use when the underlying [`Handle`] is known to be for a send half.
#[derive(Debug, Copy, Clone, PartialEq, Serialize, Deserialize)]
pub struct WriteHandle {
    pub handle: Handle,
}

// Build a chunk of memory that is suitable for passing to oak_abi::wait_on_channels,
// holding the given collection of channel handles.
fn new_handle_space(handles: &[ReadHandle]) -> Vec<u8> {
    let mut space = Vec::with_capacity(oak_abi::SPACE_BYTES_PER_HANDLE * handles.len());
    for handle in handles {
        space
            .write_u64::<byteorder::LittleEndian>(handle.handle.id)
            .unwrap();
        space.push(0x00);
    }
    space
}

// Prepare a handle space for polling by clearing all of the message-pending
// indicator bytes.
fn prep_handle_space(space: &mut [u8]) {
    let count = space.len() / 8;
    for i in 0..count {
        space[i * oak_abi::SPACE_BYTES_PER_HANDLE + (oak_abi::SPACE_BYTES_PER_HANDLE - 1)] = 0;
    }
}

/// Wait for one or more of the provided handles to become ready for reading
/// from.  On success, the returned vector of [`ChannelReadStatus`] values
/// will be in 1-1 correspondence with the passed-in vector of [`Handle`]s.
///
/// This is a convenience wrapper around the [`oak_abi::wait_on_channels`] host
/// function. This version is easier to use in Rust but is less efficient
/// (because the notification space is re-created on each invocation).
pub fn wait_on_channels(handles: &[ReadHandle]) -> Result<Vec<ChannelReadStatus>, OakStatus> {
    let mut space = new_handle_space(handles);
    unsafe {
        let status = oak_abi::wait_on_channels(space.as_mut_ptr(), handles.len() as u32);
        match OakStatus::from_i32(status as i32) {
            Some(OakStatus::OK) => (),
            Some(err) => return Err(err),
            None => return Err(OakStatus::OAK_STATUS_UNSPECIFIED),
        }
        let mut results = Vec::with_capacity(handles.len());
        for i in 0..handles.len() {
            match space
                .get(i * oak_abi::SPACE_BYTES_PER_HANDLE + (oak_abi::SPACE_BYTES_PER_HANDLE - 1))
                .cloned()
                .map(i32::from)
                .and_then(ChannelReadStatus::from_i32)
            {
                Some(status) => results.push(status),
                None => return Err(OakStatus::OAK_STATUS_UNSPECIFIED),
            }
        }
        Ok(results)
    }
}

/// Read a message from a channel.
///
/// The provided vectors for received data and associated handles will be
/// resized to accomodate the information in the message.
pub fn channel_read(half: ReadHandle, buf: &mut Vec<u8>, handles: &mut Vec<Handle>) -> OakStatus {
    // Try reading from the channel twice: first with provided vectors, then
    // with vectors that have been resized to meet size requirements.

    // We cannot deserialize directly into the handles vector because `Handle` may
    // not have the correct memory layout.
    let mut handles_buf = Vec::with_capacity(handles.capacity() * 8);
    for resized in &[false, true] {
        let mut actual_size: u32 = 0;
        let mut actual_handle_count: u32 = 0;
        let status = OakStatus::from_i32(unsafe {
            oak_abi::channel_read(
                half.handle.id,
                buf.as_mut_ptr(),
                buf.capacity(),
                &mut actual_size,
                handles_buf.as_mut_ptr(),
                handles_buf.capacity() as u32 / 8, // Handle count, not byte count
                &mut actual_handle_count,
            ) as i32
        });

        match status {
            Some(s) => match s {
                OakStatus::OK | OakStatus::ERR_CHANNEL_EMPTY => {
                    unsafe {
                        buf.set_len(actual_size as usize);

                        // actual_handle_count is number of handles not bytes
                        handles_buf.set_len(actual_handle_count as usize * 8);
                        Handle::unpack(&handles_buf, actual_handle_count, handles);
                    };
                    return s;
                }

                OakStatus::ERR_BUFFER_TOO_SMALL | OakStatus::ERR_HANDLE_SPACE_TOO_SMALL
                    if !(*resized) =>
                {
                    // Extend the vectors to be large enough for the message
                    debug!(
                        "Got space for {} bytes, need {}",
                        buf.capacity(),
                        actual_size
                    );
                    if (actual_size as usize) > buf.capacity() {
                        let extra = (actual_size as usize) - buf.len();
                        buf.reserve(extra);
                    }

                    let handles_capacity = handles_buf.capacity() / 8;
                    debug!(
                        "Got space for {} handles, need {}",
                        handles_capacity, actual_handle_count
                    );
                    if (actual_handle_count as usize) > handles_capacity {
                        let extra = (actual_handle_count as usize * 8) - handles_buf.len();
                        handles_buf.reserve(extra);
                    }

                    // Try again with a buffer resized to cope with expected size of data.
                    continue;
                }
                s => {
                    return s;
                }
            },
            None => {
                return OakStatus::ERR_INTERNAL;
            }
        }
    }
    error!("unreachable code reached");
    OakStatus::ERR_INTERNAL
}

/// Write a message to a channel.
pub fn channel_write(half: WriteHandle, buf: &[u8], handles: &[Handle]) -> OakStatus {
    let handle_buf = Handle::pack(handles);
    match OakStatus::from_i32(unsafe {
        oak_abi::channel_write(
            half.handle.id,
            buf.as_ptr(),
            buf.len(),
            handle_buf.as_ptr(),
            handles.len() as u32, // Number of handles, not bytes
        ) as i32
    }) {
        Some(s) => s,
        None => OakStatus::ERR_INTERNAL,
    }
}

/// Create a new unidirectional channel.
///
/// On success, returns [`WriteHandle`] and a [`ReadHandle`] values for the
/// write and read halves (respectively).
pub fn channel_create() -> Result<(WriteHandle, ReadHandle), OakStatus> {
    let mut write = WriteHandle {
        handle: Handle::invalid(),
    };
    let mut read = ReadHandle {
        handle: Handle::invalid(),
    };
    match OakStatus::from_i32(unsafe {
        oak_abi::channel_create(
            &mut write.handle.id as *mut u64,
            &mut read.handle.id as *mut u64,
        ) as i32
    }) {
        Some(OakStatus::OK) => Ok((write, read)),
        Some(err) => Err(err),
        None => Err(OakStatus::OAK_STATUS_UNSPECIFIED),
    }
}

/// Close the specified channel [`Handle`].
pub fn channel_close(handle: Handle) -> OakStatus {
    match OakStatus::from_i32(unsafe { oak_abi::channel_close(handle.id) as i32 }) {
        Some(s) => s,
        None => OakStatus::OAK_STATUS_UNSPECIFIED,
    }
}

/// Create a new Node running the configuration identified by `config_name`,
/// passing it the given handle.
pub fn node_create(config_name: &str, half: ReadHandle) -> OakStatus {
    match OakStatus::from_i32(unsafe {
        oak_abi::node_create(config_name.as_ptr(), config_name.len(), half.handle.id) as i32
    }) {
        Some(s) => s,
        None => OakStatus::OAK_STATUS_UNSPECIFIED,
    }
}

/// Fill a buffer with random data.
pub fn random_get(buf: &mut [u8]) -> OakStatus {
    match OakStatus::from_i32(unsafe { oak_abi::random_get(buf.as_mut_ptr(), buf.len()) as i32 }) {
        Some(s) => s,
        None => OakStatus::OAK_STATUS_UNSPECIFIED,
    }
}

/// Install a panic hook that logs [panic information].
///
/// Logs panic infomation to the logging channel, if one is set.
///
/// [panic information]: std::panic::PanicInfo
pub fn set_panic_hook() {
    std::panic::set_hook(Box::new(|panic_info| {
        let msg = panic_info
            .payload()
            .downcast_ref::<&str>()
            .unwrap_or(&"<UNKNOWN MESSAGE>");
        let (file, line) = match panic_info.location() {
            Some(location) => (location.file(), location.line()),
            None => ("<UNKNOWN FILE>", 0),
        };
        error!(
            "panic occurred in file '{}' at line {}: {}",
            file, line, msg
        );
    }));
}
