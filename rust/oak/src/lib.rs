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
use proto::oak_api::{ChannelHandle, OakStatus};
use protobuf::{Message, ProtobufEnum};
use std::io;
use std::io::Write;

pub mod proto;
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

type Handle = u64;

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
        Some(OakStatus::ERR_OUT_OF_RANGE) => {
            Err(io::Error::new(io::ErrorKind::NotConnected, "Out of range"))
        }
        None => Err(io::Error::new(
            io::ErrorKind::Other,
            "Unknown Oak status value",
        )),
    }
}

// TODO: Implement panic handler.

mod wasm {
    // See https://rustwasm.github.io/book/reference/js-ffi.html
    #[link(wasm_import_module = "oak")]
    extern "C" {
        pub fn wait_on_channels(buf: *mut u8, count: u32) -> i32;
        pub fn channel_read(handle: u64, buf: *mut u8, size: usize, actual_size: *mut u32) -> i32;
        pub fn channel_write(handle: u64, buf: *const u8, size: usize) -> i32;
    }
}

const SPACE_BYTES_PER_HANDLE: usize = 9;

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

pub struct SendChannelHalf {
    handle: Handle,
}

impl SendChannelHalf {
    pub fn new(handle: Handle) -> SendChannelHalf {
        SendChannelHalf { handle }
    }

    pub fn write_message(&mut self, buf: &[u8]) -> std::io::Result<()> {
        result_from_status(
            OakStatus::from_i32(unsafe {
                wasm::channel_write(self.handle, buf.as_ptr(), buf.len())
            }),
            (),
        )
    }
}

// Implement the Write trait on a send channel for convenience, particularly for
// the logging channel.
impl Write for SendChannelHalf {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match self.write_message(buf) {
            Ok(_) => Ok(buf.len()),
            Err(e) => Err(e),
        }
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

pub fn logging_channel() -> impl Write {
    let logging_channel = SendChannelHalf::new(ChannelHandle::LOGGING as Handle);
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

    pub fn read_message(&mut self, buf: &mut Vec<u8>) -> std::io::Result<usize> {
        // Try reading from the channel twice: first with provided vector,
        // then with a vector that's been resized to meet size requirements.
        for resized in &[false, true] {
            let mut actual_size: u32 = 0;
            let status = OakStatus::from_i32(unsafe {
                wasm::channel_read(
                    self.handle,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    &mut actual_size,
                )
            });
            match status {
                Some(OakStatus::OK) => {
                    unsafe {
                        buf.set_len(actual_size as usize);
                    };
                    return Ok(actual_size as usize);
                }
                Some(OakStatus::ERR_BUFFER_TOO_SMALL) => {
                    if *resized {
                        return result_from_status(status, 0);
                    }
                    // Can escape the match if buffer is too small and !resized.
                }
                _ => return result_from_status(status, 0),
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

/// Convenience wrapper for a send/receive pair of channels.
pub struct ChannelPair {
    pub receive: ReceiveChannelHalf,
    pub send: SendChannelHalf,
}

impl ChannelPair {
    pub fn new(in_handle: Handle, out_handle: Handle) -> ChannelPair {
        ChannelPair {
            receive: ReceiveChannelHalf::new(in_handle),
            send: SendChannelHalf::new(out_handle),
        }
    }
}

/// Trait encapsulating the operations required for an Oak Node.
pub trait OakNode {
    fn new() -> Self
    where
        Self: Sized;
    fn invoke(&mut self, method: &str, req: &[u8], out: &mut SendChannelHalf);
}

/// Perform an event loop invoking the given node.
pub fn event_loop<T: OakNode>(mut node: T) -> i32 {
    info!("start event loop for node");
    set_panic_hook();

    let read_handles = vec![ChannelHandle::GRPC_IN as Handle];
    let mut space = new_handle_space(&read_handles);

    let mut grpc_in_channel = ReceiveChannelHalf::new(ChannelHandle::GRPC_IN as Handle);
    loop {
        // Block until there is a message to read on an input channel.
        prep_handle_space(&mut space);
        unsafe {
            let status = wasm::wait_on_channels(space.as_mut_ptr(), read_handles.len() as u32);
            match OakStatus::from_i32(status) {
                Some(OakStatus::OK) => (),
                Some(err) => return err as i32,
                None => return OakStatus::OAK_STATUS_UNSPECIFIED as i32,
            }
        }

        let mut buf = Vec::<u8>::with_capacity(1024);
        grpc_in_channel.read_message(&mut buf).unwrap();
        if buf.is_empty() {
            info!("no pending message; poll again");
            continue;
        }
        let req: proto::grpc_encap::GrpcRequest = protobuf::parse_from_bytes(&buf).unwrap();
        if !req.last {
            panic!("Support for streaming requests not yet implemented");
        }
        node.invoke(
            &req.method_name,
            req.get_req_msg().value.as_slice(),
            &mut SendChannelHalf::new(ChannelHandle::GRPC_OUT as Handle),
        );
    }
}

/// Install a panic hook so that panics are logged to the logging channel, if one is set.
/// See https://doc.rust-lang.org/std/panic/struct.PanicInfo.html.
fn set_panic_hook() {
    std::panic::set_hook(Box::new(|panic_info| {
        let msg = panic_info
            .payload()
            .downcast_ref::<&str>()
            .unwrap_or(&"<UNKWOWN MESSAGE>");
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
