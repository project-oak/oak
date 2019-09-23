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

extern crate byteorder;
extern crate fmt;
#[macro_use]
extern crate log;
extern crate protobuf;

use byteorder::WriteBytesExt;
use proto::oak_api::OakStatus;
use protobuf::{Message, ProtobufEnum};
use std::io;
use std::io::Write;

pub mod proto;
pub mod storage;
#[cfg(test)]
mod tests;

#[cfg(test)]
#[macro_use]
extern crate assert_matches;

pub type GrpcResult<T> = Result<T, proto::status::Status>;

/// Trait to allow repeated writing of responses for server-streaming gRPC methods.
pub trait ResponseWriter<T: protobuf::Message> {
    fn write(&mut self, rsp: T);
}

/// Implementation of ResponseWriter that encapsulates response messages into
/// GrpcResponse wrapper messages and writes serialized versions to a (mutably
/// borrowed) send channel.
pub struct ChannelResponseWriter<'a> {
    pub channel: &'a mut SendChannelHalf,
}

impl<'a, T> ResponseWriter<T> for ChannelResponseWriter<'a>
where
    T: protobuf::Message,
{
    fn write(&mut self, rsp: T) {
        // Put the serialized response into a GrpcResponse message wrapper.
        let mut grpc_rsp = proto::grpc_encap::GrpcResponse::new();
        let mut any = protobuf::well_known_types::Any::new();
        rsp.write_to_writer(&mut any.value).unwrap();
        grpc_rsp.set_rsp_msg(any);
        // Serialize the GrpcResponse into the send channel.
        grpc_rsp.write_to_writer(&mut self.channel).unwrap();
    }
}

pub type Handle = u64;

/// Map an OakStatus to the nearest available std::io::Result.
fn result_from_status<T>(status: Option<OakStatus>, val: T) -> std::io::Result<T> {
    match status {
        Some(OakStatus::OAK_STATUS_UNSPECIFIED) => Err(io::Error::new(
            io::ErrorKind::Other,
            "Unspecified Oak status value",
        )),
        Some(OakStatus::OK) => Ok(val),
        Some(OakStatus::ERR_BAD_HANDLE) => {
            Err(io::Error::new(io::ErrorKind::NotConnected, "Bad handle"))
        }
        Some(OakStatus::ERR_INVALID_ARGS) => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "Invalid arguments",
        )),
        Some(OakStatus::ERR_CHANNEL_CLOSED) => Err(io::Error::new(
            io::ErrorKind::ConnectionReset,
            "Channel closed",
        )),
        Some(OakStatus::ERR_BUFFER_TOO_SMALL) => Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "Buffer too small",
        )),
        Some(OakStatus::ERR_HANDLE_SPACE_TOO_SMALL) => Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "Handle space too small",
        )),
        Some(OakStatus::ERR_OUT_OF_RANGE) => {
            Err(io::Error::new(io::ErrorKind::NotConnected, "Out of range"))
        }
        Some(OakStatus::ERR_INTERNAL) => {
            Err(io::Error::new(io::ErrorKind::Other, "Internal error"))
        }
        None => Err(io::Error::new(
            io::ErrorKind::Other,
            "Unknown Oak status value",
        )),
    }
}

mod wasm {
    // See https://rustwasm.github.io/book/reference/js-ffi.html
    #[link(wasm_import_module = "oak")]
    extern "C" {
        pub fn wait_on_channels(buf: *mut u8, count: u32) -> i32;
        pub fn channel_read(
            handle: u64,
            buf: *mut u8,
            size: usize,
            actual_size: *mut u32,
            handle_buf: *mut u8,
            handle_count: usize,
            actual_handle_count: *mut u32,
        ) -> i32;
        pub fn channel_write(
            handle: u64,
            buf: *const u8,
            size: usize,
            handle_buf: *const u8,
            handle_count: usize,
        ) -> i32;
        pub fn channel_create(write: *mut u64, read: *mut u64) -> i32;
        pub fn channel_close(handle: u64) -> i32;
        pub fn channel_find(buf: *const u8, len: usize) -> u64;
    }
}

pub fn channel_create() -> Result<(Handle, Handle), OakStatus> {
    let mut write: Handle = 0;
    let mut read: Handle = 0;
    match OakStatus::from_i32(unsafe {
        wasm::channel_create(&mut write as *mut u64, &mut read as *mut u64) // @@@ check endianness
    }) {
        Some(OakStatus::OK) => Ok((write, read)),
        Some(err) => Err(err),
        None => Err(OakStatus::OAK_STATUS_UNSPECIFIED),
    }
}

pub fn channel_close(handle: Handle) -> OakStatus {
    match OakStatus::from_i32(unsafe { wasm::channel_close(handle) }) {
        Some(s) => s,
        None => OakStatus::OAK_STATUS_UNSPECIFIED,
    }
}

pub fn channel_find(port_name: &str) -> Handle {
    unsafe { wasm::channel_find(port_name.as_ptr(), port_name.len()) }
}

pub const SPACE_BYTES_PER_HANDLE: usize = 9;

// Build a chunk of memory that is suitable for passing to wasm::wait_on_channels,
// holding the given collection of channel handles.
fn new_handle_space(handles: &[Handle]) -> Vec<u8> {
    let mut space = Vec::with_capacity(SPACE_BYTES_PER_HANDLE * handles.len());
    for handle in handles {
        space.write_u64::<byteorder::LittleEndian>(*handle).unwrap();
        space.push(0x00);
    }
    space
}

// Prepare a handle space for polling by clearing all of the message-pending
// indicator bytes.
fn prep_handle_space(space: &mut [u8]) {
    let count = space.len() / 8;
    for i in 0..count {
        space[i * SPACE_BYTES_PER_HANDLE + (SPACE_BYTES_PER_HANDLE - 1)] = 0;
    }
}

// Convenience wrapper around wait_on_channels host function. This version is
// easier to use in Rust but is less efficient (because the notification space
// is re-created on each invocation).
pub fn wait_on_channels(handles: &[Handle]) -> Result<Vec<Handle>, OakStatus> {
    let mut space = new_handle_space(handles);
    unsafe {
        let status = wasm::wait_on_channels(space.as_mut_ptr(), handles.len() as u32);
        match OakStatus::from_i32(status) {
            Some(OakStatus::OK) => (),
            Some(err) => return Err(err),
            None => return Err(OakStatus::OAK_STATUS_UNSPECIFIED),
        }
        let mut results = Vec::with_capacity(handles.len());
        for i in 0..handles.len() {
            if space[i * SPACE_BYTES_PER_HANDLE + (SPACE_BYTES_PER_HANDLE - 1)] != 0 {
                results.push(handles[i]);
            }
        }
        Ok(results)
    }
}

pub struct SendChannelHalf {
    handle: Handle,
}

impl SendChannelHalf {
    pub fn new(handle: Handle) -> SendChannelHalf {
        SendChannelHalf { handle }
    }

    pub fn write_message(&mut self, buf: &[u8], handles: &[Handle]) -> std::io::Result<()> {
        result_from_status(
            OakStatus::from_i32(unsafe {
                wasm::channel_write(
                    self.handle,
                    buf.as_ptr(),
                    buf.len(),
                    handles.as_ptr() as *const u8, // Wasm spec defines this as little-endian
                    handles.len(),
                )
            }),
            (),
        )
    }
}

// Implement the Write trait on a send channel for convenience, particularly for
// the logging channel.
impl Write for SendChannelHalf {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match self.write_message(buf, &[]) {
            Ok(_) => Ok(buf.len()),
            Err(e) => Err(e),
        }
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

pub fn logging_channel() -> impl Write {
    let logging_channel = SendChannelHalf::new(channel_find("log"));
    // Only flush logging channel on newlines.
    std::io::LineWriter::new(logging_channel)
}

pub struct ReceiveChannelHalf {
    handle: Handle,
}

impl ReceiveChannelHalf {
    pub fn new(handle: Handle) -> ReceiveChannelHalf {
        ReceiveChannelHalf { handle }
    }

    pub fn read_message(
        &mut self,
        buf: &mut Vec<u8>,
        handles: &mut Vec<Handle>,
    ) -> std::io::Result<()> {
        // Try reading from the channel twice: first with provided vectors, then
        // with vectors that have been resized to meet size requirements.
        for resized in &[false, true] {
            let mut actual_size: u32 = 0;
            let mut actual_handle_count: u32 = 0;
            let status = OakStatus::from_i32(unsafe {
                wasm::channel_read(
                    self.handle,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    &mut actual_size,
                    handles.as_mut_ptr() as *mut u8,
                    handles.capacity(),
                    &mut actual_handle_count,
                )
            });
            match status {
                Some(OakStatus::OK) => {
                    unsafe {
                        buf.set_len(actual_size as usize);
                        // Handles are written in little-endian order, which matches Wasm spec
                        handles.set_len(actual_handle_count as usize);
                    };
                    return Ok(());
                }
                Some(OakStatus::ERR_BUFFER_TOO_SMALL) => {
                    if *resized {
                        return result_from_status(status, ());
                    }
                    // Can escape the match if buffer is too small and !resized.
                }
                _ => return result_from_status(status, ()),
            }

            // Extend the vector to be large enough for the message
            debug!("Got {}, need {}", buf.capacity(), actual_size);
            if (actual_size as usize) < buf.len() {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    format!(
                        "Internal error: provided {} bytes for receive, asked for {}",
                        buf.len(),
                        actual_size
                    ),
                ));
            }
            let extra = (actual_size as usize) - buf.len();
            buf.reserve(extra);
        }
        Err(io::Error::new(io::ErrorKind::Other, "Unreachable reached!"))
    }
}

/// Trait encapsulating the operations required for an Oak Node.
pub trait OakNode {
    fn new() -> Self
    where
        Self: Sized;
    fn invoke(&mut self, method: &str, req: &[u8], out: &mut SendChannelHalf);
}

/// Perform a gRPC event loop on the given channels, invoking the given node.
pub fn grpc_event_loop<T: OakNode>(
    mut node: T,
    grpc_in_handle: Handle,
    grpc_out_handle: Handle,
) -> i32 {
    info!(
        "start event loop for node with handles in:{} out:{}",
        grpc_in_handle, grpc_out_handle
    );
    if grpc_in_handle == 0 || grpc_out_handle == 0 {
        return OakStatus::ERR_CHANNEL_CLOSED.value();
    }
    set_panic_hook();

    let read_handles = vec![grpc_in_handle];
    let mut space = new_handle_space(&read_handles);

    let mut grpc_in_channel = ReceiveChannelHalf::new(grpc_in_handle);
    let mut grpc_out_channel = SendChannelHalf::new(grpc_out_handle);
    loop {
        // Block until there is a message to read on an input channel.
        prep_handle_space(&mut space);
        unsafe {
            let status = wasm::wait_on_channels(space.as_mut_ptr(), read_handles.len() as u32);
            match OakStatus::from_i32(status) {
                Some(OakStatus::OK) => (),
                Some(err) => return err as i32,
                None => return OakStatus::OAK_STATUS_UNSPECIFIED.value(),
            }
        }

        let mut buf = Vec::<u8>::with_capacity(1024);
        let mut handles = Vec::<Handle>::with_capacity(1);
        grpc_in_channel
            .read_message(&mut buf, &mut handles)
            .unwrap();
        if buf.is_empty() {
            info!("no pending message; poll again");
            continue;
        }
        if !handles.is_empty() {
            panic!("unexpected handles received alongside gRPC response")
        }
        let req: proto::grpc_encap::GrpcRequest = protobuf::parse_from_bytes(&buf).unwrap();
        if !req.last {
            panic!("Support for streaming requests not yet implemented");
        }
        node.invoke(
            &req.method_name,
            req.get_req_msg().value.as_slice(),
            &mut grpc_out_channel,
        );
    }
}

/// Install a panic hook so that panics are logged to the logging channel, if one is set.
/// See https://doc.rust-lang.org/std/panic/struct.PanicInfo.html.
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
