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

use std::cell::RefCell;
use std::io::{Read, Write};

type Handle = u64;

// Keep in sync with /oak/server/oak_node.h.
pub const LOGGING_CHANNEL_HANDLE: Handle = 1;
pub const GRPC_CHANNEL_HANDLE: Handle = 2;
pub const GRPC_METHOD_NAME_CHANNEL_HANDLE: Handle = 3;

// TODO: Implement panic handler.

mod wasm {
    // See https://rustwasm.github.io/book/reference/js-ffi.html
    #[link(wasm_import_module = "oak")]
    extern "C" {
        pub fn channel_read(handle: u64, buf: *mut u8, size: usize) -> usize;
        pub fn channel_write(handle: u64, buf: *const u8, size: usize) -> usize;
    }
}

pub struct Channel {
    handle: Handle,
}

impl Channel {
    pub fn new(handle: Handle) -> Channel {
        Channel { handle: handle }
    }
}

pub fn logging_channel() -> impl Write {
    let mut logging_channel = Channel::new(LOGGING_CHANNEL_HANDLE);
    // Only flush logging channel on newlines.
    std::io::LineWriter::new(logging_channel)
}

impl Read for Channel {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Ok(unsafe { wasm::channel_read(self.handle, buf.as_mut_ptr(), buf.len()) })
    }
}

impl Write for Channel {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Ok(unsafe { wasm::channel_write(self.handle, buf.as_ptr(), buf.len()) })
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// Trait encapsulating the operations required for an Oak Node.
pub trait Node {
    fn new() -> Self
    where
        Self: Sized;
    fn invoke(&mut self, grpc_method_name: &str, grpc_channel: &mut Channel);
}

/// No-op implementation of Node, so that we have a placeholder value until the actual one is set
/// via `set_node`.
struct NopNode;

impl Node for NopNode {
    fn new() -> Self {
        NopNode
    }
    fn invoke(&mut self, _grpc_method_name: &str, _grpc_channel: &mut Channel) {}
}

thread_local! {
    static NODE: RefCell<Box<dyn Node>> = RefCell::new(Box::new(NopNode));
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
///     fn invoke(&mut self, grpc_method_name: &str, grpc_channel: &mut oak::Channel) { /* ... */ }
/// }
///
/// #[no_mangle]
/// pub extern "C" fn oak_initialize() {
///     oak::set_node::<Node>();
/// }
/// ```
pub fn set_node<T: Node + 'static>() {
    // TODO: Detect multiple invocations.
    NODE.with(|node| {
        *node.borrow_mut() = Box::new(T::new());
    });
}

#[no_mangle]
pub extern "C" fn oak_handle_grpc_call() {
    NODE.with(|node| {
        let mut grpc_method_channel = Channel::new(GRPC_METHOD_NAME_CHANNEL_HANDLE);
        let mut grpc_method_name = String::new();
        grpc_method_channel.read_to_string(&mut grpc_method_name);
        let mut grpc_channel = Channel::new(GRPC_CHANNEL_HANDLE);
        node.borrow_mut()
            .invoke(&grpc_method_name, &mut grpc_channel);
    });
}
