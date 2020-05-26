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

//! Stub definitions of the ABI symbols, to allow Oak Node code to be built
//! on the host platform.
//!
//! When building the Rust code for an Oak Node, the resulting library code
//! references the functions provided by the Oak ABI.
//!
//! For the target Wasm platform, these Oak ABI functions are provided as Wasm
//! host functions by the Oak Runtime; however, the Runtime is not available
//! when compiling on the host platform.
//!
//! On some host platforms (e.g. `target_os = "linux"`), linking a library that
//! references as-yet undefined symbols is allowed; those symbol just have to
//! be present at the point when the final binary is linked.
//!
//! However, on other host platforms (notably OS X, `target_os = "macos"`), the
//! library can only be linked if a definition of these ABI functions is
//! available at *library* link time. More discussion at:
//! https://github.com/rust-lang/rust/pull/66204
//!
//! This module therefore provides stub definitions of the ABI functions for
//! those host platforms that need them at library link time, so that `cargo
//! build` works.

#[no_mangle]
pub extern "C" fn wait_on_channels(_buf: *mut u8, _count: u32) -> u32 {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn channel_read(
    _handle: u64,
    _buf: *mut u8,
    _size: usize,
    _actual_size: *mut u32,
    _handle_buf: *mut u8,
    _handle_count: u32,
    _actual_handle_count: *mut u32,
) -> u32 {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn channel_write(
    _handle: u64,
    _buf: *const u8,
    _size: usize,
    _handle_buf: *const u8,
    _handle_count: u32,
) -> u32 {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn channel_create(_write: *mut u64, _read: *mut u64) -> u32 {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn channel_close(_handle: u64) -> u32 {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn node_create(_config_buf: *const u8, _config_len: usize, _handle: u64) -> u32 {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn random_get(_buf: *mut u8, _len: usize) -> u32 {
    panic!("stub function invoked!");
}
