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

mod wasm {
    // See https://rustwasm.github.io/book/reference/js-ffi.html
    #[link(wasm_import_module = "oak")]
    extern "C" {
        pub fn open_channel(name: *const u8, size: usize) -> u64;
        pub fn close_channel(channel_id: u64);

        pub fn read_channel(channel_id: u64, buf: *mut u8, size: usize) -> usize;
        pub fn write_channel(channel_id: u64, buf: *const u8, size: usize) -> usize;
    }
}

pub struct Channel {
    channel_id: u64,
}

impl Channel {
    fn open(name: &str) -> Channel {
        let channel_id = unsafe { wasm::open_channel(name.as_ptr(), name.len()) };
        Channel {
            channel_id: channel_id,
        }
    }
}

impl Drop for Channel {
    fn drop(&mut self) {
        //unsafe { wasm::close_channel(self.channel_id) };
    }
}

impl Read for Channel {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Ok(unsafe { wasm::read_channel(self.channel_id, buf.as_mut_ptr(), buf.len()) })
    }
}

impl Write for Channel {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Ok(unsafe { wasm::write_channel(self.channel_id, buf.as_ptr(), buf.len()) })
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn grpc_method_name() -> String {
    let mut c = Channel::open("grpc_method_name");
    let mut buffer = String::new();
    // TODO: Check errors.
    c.read_to_string(&mut buffer);
    buffer
}

pub fn print(s: &str) {
    let mut c = Channel::open("print");
    c.write(s.as_bytes());
}

pub fn get_time() -> std::time::SystemTime {
    let ns = 11; // unsafe { wasm::get_time() };
    std::time::UNIX_EPOCH + std::time::Duration::from_nanos(ns)
}

/// Trait encapsulating the operations required for an Oak Node.
pub trait Node {
    fn new() -> Self
    where
        Self: Sized;
    fn invoke(&mut self, grpc_method_name: &str, grpc: &mut Channel);
}

/// No-op implementation of Node, so that we have a placeholder value until the actual one is set
/// via `set_node`.
struct NopNode;

impl Node for NopNode {
    fn new() -> Self {
        NopNode
    }
    fn invoke(&mut self, _grpc_method_name: &str, _grpc: &mut Channel) {}
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
///     fn invoke(&mut self, grpc_method_name: &str, request: &mut oak::Reader, response: &mut oak::Writer) { /* ... */ }
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
pub extern "C" fn oak_handle_grpc_call(grpc_channel_id: u64) {
    NODE.with(|node| {
        let method_name = grpc_method_name();
        let mut grpc_channel = Channel {
            channel_id: grpc_channel_id,
        };
        node.borrow_mut().invoke(&method_name, &mut grpc_channel);
    });
}
