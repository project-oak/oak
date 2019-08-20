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

extern crate fmt;
#[macro_use]
extern crate log;
extern crate protobuf;

use protobuf::Message;
use std::cell::RefCell;
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

// Keep in sync with /oak/server/oak_node.h.
pub const LOGGING_CHANNEL_HANDLE: Handle = 1;
pub const GRPC_IN_CHANNEL_HANDLE: Handle = 2;
pub const GRPC_OUT_CHANNEL_HANDLE: Handle = 3;

// Status values returned across the host function interface
#[derive(Debug, PartialEq)]
pub enum Status {
    Ok,
    BadHandle,
    InvalidArgs,
    ChannelClosed,
    BufferTooSmall,
    OutOfRange,
    Unknown(i32),
}

fn status_from_i32(raw: i32) -> Status {
    // Keep in sync with /oak/server/status.h
    match raw {
        0 => Status::Ok,
        1 => Status::BadHandle,
        2 => Status::InvalidArgs,
        3 => Status::ChannelClosed,
        4 => Status::BufferTooSmall,
        5 => Status::OutOfRange,
        _ => Status::Unknown(raw),
    }
}

/// Map a host function status to the nearest available std::io::Result.
fn result_from_status<T>(status: Status, val: T) -> std::io::Result<T> {
    match status {
        Status::Ok => Ok(val),
        Status::BadHandle => Err(io::Error::new(io::ErrorKind::NotConnected, "Bad handle")),
        Status::InvalidArgs => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "Invalid arguments",
        )),
        Status::ChannelClosed => Err(io::Error::new(
            io::ErrorKind::ConnectionReset,
            "Channel closed",
        )),
        Status::BufferTooSmall => Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "Buffer too small",
        )),
        Status::OutOfRange => Err(io::Error::new(io::ErrorKind::NotConnected, "Out of range")),
        Status::Unknown(raw) => Err(io::Error::new(
            io::ErrorKind::Other,
            format!("Unknown Oak status value {}", raw),
        )),
    }
}

// TODO: Implement panic handler.

mod wasm {
    // See https://rustwasm.github.io/book/reference/js-ffi.html
    #[link(wasm_import_module = "oak")]
    extern "C" {
        pub fn channel_read(handle: u64, buf: *mut u8, size: usize, actual_size: *mut u32) -> i32;
        pub fn channel_write(handle: u64, buf: *const u8, size: usize) -> i32;
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
            status_from_i32(unsafe { wasm::channel_write(self.handle, buf.as_ptr(), buf.len()) }),
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
    let logging_channel = SendChannelHalf::new(LOGGING_CHANNEL_HANDLE);
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
            let status = status_from_i32(unsafe {
                wasm::channel_read(
                    self.handle,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    &mut actual_size,
                )
            });
            match status {
                Status::Ok => {
                    unsafe {
                        buf.set_len(actual_size as usize);
                    };
                    return Ok(actual_size as usize);
                }
                Status::BufferTooSmall => {
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

thread_local! {
    static NODE: RefCell<Option<Box<dyn OakNode>>> = RefCell::new(None);
}

/// Sets the Oak Node to execute in the current instance.
///
/// This function may only be called once, and only from an exported `oak_initialize` function:
///
/// ```rust
/// struct Node;
///
/// impl oak::OakNode for Node {
///     fn new() -> Self { Node }
///     fn invoke(&mut self, method: &str, req: &[u8], out: &mut oak::SendChannelHalf) { /* ... */ }
/// }
///
/// #[no_mangle]
/// pub extern "C" fn oak_initialize() {
///     oak::set_node::<Node>();
/// }
/// ```
pub fn set_node<T: OakNode + 'static>() {
    set_panic_hook();
    NODE.with(|node| {
        match *node.borrow_mut() {
            Some(_) => {
                writeln!(logging_channel(), "attempt to set_node() when already set!").unwrap();
                panic!("attempt to set_node when already set");
            }
            None => {
                writeln!(logging_channel(), "setting current node instance").unwrap();
            }
        }
        *node.borrow_mut() = Some(Box::new(T::new()));
    });
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

#[no_mangle]
pub extern "C" fn oak_handle_grpc_call() {
    NODE.with(|node| match *node.borrow_mut() {
        Some(ref mut node) => {
            let mut buf = Vec::<u8>::with_capacity(1024);
            let mut grpc_in_channel = ReceiveChannelHalf::new(GRPC_IN_CHANNEL_HANDLE);
            grpc_in_channel.read_message(&mut buf).unwrap();
            let req: proto::grpc_encap::GrpcRequest = protobuf::parse_from_bytes(&buf).unwrap();
            if !req.last {
                panic!("Support for streaming requests not yet implemented");
            }
            node.invoke(
                &req.method_name,
                req.get_req_msg().value.as_slice(),
                &mut SendChannelHalf::new(GRPC_OUT_CHANNEL_HANDLE),
            );
        }
        None => {
            writeln!(logging_channel(), "gRPC call with no loaded Node").unwrap();
            panic!("gRPC call with no loaded Node");
        }
    });
}

/// Return whether an Oak Node is currently available.
pub fn have_node() -> bool {
    NODE.with(|node| (*node.borrow()).is_some())
}

#[test]
fn reset_node() {
    NODE.with(|node| {
        *node.borrow_mut() = None;
    })
}
