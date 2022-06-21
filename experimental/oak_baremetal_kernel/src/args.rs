//
// Copyright 2022 The Project Oak Authors
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

use arrayvec::ArrayString;
use core::ffi::CStr;

static mut ARGS: ArrayString<512> = ArrayString::new_const();

/// Buffers kernel arguments in a static variable.
///
/// This function is intended to be called fairly early in the boot process, when we don't even
/// have memory allocation available. This also means that we can't use anyhow::Result as the
/// return value, as anyhow relies on allocation.
pub fn init_args(args: &CStr) -> core::result::Result<(), &str> {
    let args = args
        .to_str()
        .map_err(|core::str::Utf8Error { .. }| "Kernel arguments are not valid UTF-8")?;
    // Safety: this is called once early in the initialization process from a single thread, so
    // there will not be any concurrent writes.
    unsafe { ARGS.try_push_str(args) }
        .map_err(|arrayvec::CapacityError { .. }| "Kernel arguments too long")
}

pub fn args() -> &'static str {
    // Safety: once init_args() has been called, the static will not be modified, so it's fine to
    // have multiple non-mut references to the memory.
    unsafe { ARGS.as_str() }
}
