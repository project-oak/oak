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

mod wasm {
    // See https://rustwasm.github.io/book/reference/js-ffi.html
    #[link(wasm_import_module = "oak")]
    extern "C" {
        pub fn print(s: &str);
        pub fn get_time() -> u64;
        pub fn read(buf: *mut u8, size: usize) -> usize;
        pub fn write(buf: *const u8, size: usize) -> usize;
        pub fn read_method_name(buf: *mut u8, size: usize) -> usize;
    }
}

fn method_name() -> String {
    // We do a single fixed-size read for the method name to simplify the server logic, so we do
    // not have to keep track of how many bytes have been read already.
    let mut buf = [0u8; 255];
    let len: usize;
    unsafe {
        len = wasm::read_method_name(buf.as_mut_ptr(), buf.len());
    }
    std::str::from_utf8(&buf[0..len])
        .expect("could not read method name")
        .to_string()
}

pub fn print(s: &str) {
    unsafe { wasm::print(s) }
}

pub fn get_time() -> std::time::SystemTime {
    let ns = unsafe { wasm::get_time() };
    std::time::UNIX_EPOCH + std::time::Duration::from_nanos(ns)
}

pub struct Reader {
    _private: (),
}

impl std::io::Read for Reader {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Ok(unsafe { wasm::read(buf.as_mut_ptr(), buf.len()) })
    }
}

pub struct Writer {
    _private: (),
}

impl std::io::Write for Writer {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Ok(unsafe { wasm::write(buf.as_ptr(), buf.len()) })
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
    fn invoke(&mut self, grpc_method_name: &str, request: &mut Reader, response: &mut Writer);
}

/// No-op implementation of Node, so that we have a placeholder value until the actual one is set
/// via `set_node`.
struct NopNode;

impl Node for NopNode {
    fn new() -> Self {
        NopNode
    }
    fn invoke(&mut self, grpc_method_name: &str, request: &mut Reader, response: &mut Writer) {}
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
pub extern "C" fn oak_handle_grpc_call() {
    NODE.with(|node| {
        let method_name = method_name();
        node.borrow_mut().invoke(
            &method_name,
            &mut Reader { _private: () },
            &mut Writer { _private: () },
        );
    });
}
