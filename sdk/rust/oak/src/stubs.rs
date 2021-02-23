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
//!
//! Note that these stub definitions do *not* need to have the correct
//! signatures, so arguments are skipped below to reduce the number of things
//! that need to be kept in sync.

#[no_mangle]
pub extern "C" fn wait_on_channels() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn wait_on_channels_with_downgrade() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn channel_read() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn channel_read_with_downgrade() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn channel_write() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn channel_write_with_downgrade() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn channel_create() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn channel_create_with_downgrade() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn channel_close() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn handle_clone() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn node_create() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn node_create_with_downgrade() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn channel_label_read() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn node_label_read() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn node_privilege_read() {
    panic!("stub function invoked!");
}
#[no_mangle]
pub extern "C" fn random_get() {
    panic!("stub function invoked!");
}
