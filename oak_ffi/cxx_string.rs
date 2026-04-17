//
// Copyright 2025 The Project Oak Authors
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

use std::os::raw::c_void;

/// A basic wrapper around Rust or C-provided bytes of known length.
///
/// This structure can be passed back and forth between Rust and C code.
///
/// A wrapper around a std::string so that it can be passed to Rust.
///
/// See the corresponding C++ implementation in cc/ffi/cxx_string.h
#[repr(C)]
pub struct CxxString {
    ptr: *const c_void,
}

// See the implementations in cc/ffi/cxx_string.h
#[link(name = "cxx_string")]
unsafe extern "C" {
    pub fn cxx_string_data(cxx_string: *const CxxString) -> *const u8;
    pub fn cxx_string_len(cxx_string: *const CxxString) -> usize;
    pub fn free_cxx_string(bytes: *const CxxString);
}

impl Drop for CxxString {
    fn drop(&mut self) {
        // # Safety
        //
        // The CxxString should not be modified or manipulated by C++ code once
        // its been passed to Rust.
        unsafe { crate::free_cxx_string(self as *const CxxString) };
    }
}

impl CxxString {
    /// Provide a view of the string as a slice for use in Rust.
    pub fn as_slice(&self) -> &[u8] {
        // # Safety
        //
        // The CxxString should not be modified or manipulated by C++ code once
        // its been passed to Rust.
        unsafe {
            std::slice::from_raw_parts(
                cxx_string_data(self as *const CxxString),
                cxx_string_len(self as *const CxxString),
            )
        }
    }
}

#[cfg(test)]
mod test {
    use oak_ffi_bytes::BytesView;

    use super::CxxString;

    unsafe extern "C" {
        fn create_test_string(name: BytesView) -> CxxString;
    }

    #[test]
    fn test_read_cxx_string() {
        let name = "CxxString Test";
        let cs = unsafe { create_test_string(BytesView::new_from_slice(name.as_bytes())) };
        assert_eq!(cs.as_slice(), b"Hello from FFI, CxxString Test");
    }
}
