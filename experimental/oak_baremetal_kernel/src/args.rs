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

extern crate alloc;

use alloc::collections::btree_map::BTreeMap;
use arrayvec::ArrayString;
use core::ffi::CStr;
use lazy_static::lazy_static;

static mut ARGS_BUF: ArrayString<512> = ArrayString::new_const();

lazy_static! {
    static ref ARGS: BTreeMap<&'static str, &'static str> = {
        let mut m = BTreeMap::new();
        args()
            .split_whitespace()
            .map(|x| x.split_once('=').unwrap_or((x, "")))
            .for_each(|(k, v)| {
                m.insert(k, v);
            });
        m
    };
}

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
    unsafe { ARGS_BUF.try_push_str(args) }
        .map_err(|arrayvec::CapacityError { .. }| "Kernel arguments too long")
}

/// Returns the kernel command line arguments.
///
/// This function may only be called after <init_args> has been called. It is safe to call this
/// function before the heap has been initialized.
pub fn args() -> &'static str {
    // Safety: once init_args() has been called, the static will not be modified, so it's fine to
    // have multiple non-mut references to the memory.
    unsafe { ARGS_BUF.as_str() }
}

/// Returns the value for the given kernel command line argument.
///
/// The syntax of the kernel command line arguments is `key=val key=val key key=val`; whitespace (or
/// lack thereof) is important!
///
/// This function may only be called after <init_args> has been called and the heap has been
/// initialized, as it allocates memory on first invocation.
pub fn arg(k: &str) -> Option<&'static str> {
    ARGS.get(k).copied()
}
