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

use atomic_refcell::AtomicRefCell;
use core::ffi::CStr;
use lazy_static::lazy_static;

// This is a really crude analogue of CString, which we can't use, as CString requires allocation.
// Instead of allocation, we rely on a static buffer.
struct StaticCString {
    buf: [u8; 512],

    // Index of \0 in the buffer, above, so that we don't have to keep searching for it.
    len: usize,
}

impl Default for StaticCString {
    fn default() -> Self {
        StaticCString {
            buf: [0; 512],
            len: 0,
        }
    }
}

impl StaticCString {
    fn as_c_str(&self) -> &CStr {
        // Safety: this is safe as initally len will be zero, resulting in an empty CStr;
        // otherwise, the fields are initialized from init_args() from a pre-existing valid CStr.
        unsafe { CStr::from_bytes_with_nul_unchecked(&self.buf[..self.len]) }
    }
}

lazy_static! {
    static ref ARGS: AtomicRefCell<StaticCString> = Default::default();
}

/// Buffers kernel arguments in a static variable.
///
/// This function is intended to be called fairly early in the boot process, when we don't even
/// have memory allocation available. This also means that we can't use anyhow::Result as the
/// return value, as anyhow relies on allocation.
pub fn init_args(args: &CStr) -> core::result::Result<(), &str> {
    let src = args.to_bytes_with_nul();
    let mut dst = ARGS.borrow_mut();

    if src.len() > dst.buf.len() {
        return Err("Kernel command line too long");
    }
    dst.len = src.len();
    dst.buf[..src.len()].copy_from_slice(src);

    Ok(())
}

pub fn args() -> &'static CStr {
    // Hack as the fact that ARGS is static is not immediately evident.
    // Safety: we initialize ARGS once, with a static buffer, so the pointer will be valid and
    // always pointing to the same memory location.
    unsafe { ARGS.as_ptr().as_ref() }.unwrap().as_c_str()
}
