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

extern crate protobuf;

use std::cell::RefCell;
use std::io::{Read, Write};

mod proto;

type Handle = u64;

// Keep in sync with /oak/server/oak_node.h.
pub const LOGGING_CHANNEL_HANDLE: Handle = 1;
pub const GRPC_METHOD_NAME_CHANNEL_HANDLE: Handle = 2;
pub const GRPC_IN_CHANNEL_HANDLE: Handle = 3;
pub const GRPC_OUT_CHANNEL_HANDLE: Handle = 4;

// TODO: Implement panic handler.

mod wasm {
    // See https://rustwasm.github.io/book/reference/js-ffi.html
    #[link(wasm_import_module = "oak")]
    extern "C" {
        pub fn channel_read(handle: u64, buf: *mut u8, size: usize) -> usize;
        pub fn channel_write(handle: u64, buf: *const u8, size: usize) -> usize;
    }
}

pub struct SendChannelHalf {
    handle: Handle,
}

impl SendChannelHalf {
    pub fn new(handle: Handle) -> SendChannelHalf {
        SendChannelHalf { handle }
    }
}

impl Write for SendChannelHalf {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Ok(unsafe { wasm::channel_write(self.handle, buf.as_ptr(), buf.len()) })
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
}

impl Read for ReceiveChannelHalf {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Ok(unsafe { wasm::channel_read(self.handle, buf.as_mut_ptr(), buf.len()) })
    }
}

/// Trait encapsulating the operations required for an Oak Node.
pub trait Node {
    fn new() -> Self
    where
        Self: Sized;
    fn invoke(
        &mut self,
        grpc_method_name: &str,
        grpc_in: &mut ReceiveChannelHalf,
        grpc_out: &mut SendChannelHalf,
    );
}

thread_local! {
    static NODE: RefCell<Option<Box<dyn Node>>> = RefCell::new(None);
}

/// Sets the Oak Node to execute in the current instance.
///
/// This function may only be called once, and only from an exported `oak_initialize` function:
///
/// ```rust
/// struct Node;
///
/// impl oak::Node for Node {
///     fn new() -> Self { Node }
///     fn invoke(&mut self, grpc_method_name: &str, grpc_in: &mut oak::ReceiveChannelHalf, grpc_out: &mut oak::SendChannelHalf) { /* ... */ }
/// }
///
/// #[no_mangle]
/// pub extern "C" fn oak_initialize() {
///     oak::set_node::<Node>();
/// }
/// ```
pub fn set_node<T: Node + 'static>() {
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

#[no_mangle]
pub extern "C" fn oak_handle_grpc_call() {
    NODE.with(|node| match *node.borrow_mut() {
        Some(ref mut node) => {
            let mut grpc_method_channel = ReceiveChannelHalf::new(GRPC_METHOD_NAME_CHANNEL_HANDLE);
            let mut grpc_method_name = String::new();
            grpc_method_channel
                .read_to_string(&mut grpc_method_name)
                .unwrap();
            let mut grpc_in = ReceiveChannelHalf::new(GRPC_IN_CHANNEL_HANDLE);
            let mut grpc_out = SendChannelHalf::new(GRPC_OUT_CHANNEL_HANDLE);
            node.invoke(&grpc_method_name, &mut grpc_in, &mut grpc_out);
        }
        None => {
            writeln!(logging_channel(), "gRPC call with no loaded Node").unwrap();
            panic!("gRPC call with no loaded Node");
        }
    });
}
