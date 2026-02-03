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

use oak_ffi_bytes::BytesView;

// An opaque representation of absl::Status.
#[repr(C)]
struct AbslStatus {
    opaque: [u8; 0],
}

/// A bridge type for functions returning absl::Status*
///
/// The contract for using this type is that C++ should return a bare
/// absl::Status* from a function called by Rust. Rust will take
/// ownership of the pointer, and this type will ensure that the memory
/// is freed when Rust is done using it.
#[repr(C)]
pub struct AbslStatusPtr {
    ptr: *const AbslStatus,
}

impl AbslStatusPtr {
    pub fn code(&self) -> u32 {
        // # Safety
        //
        // The pointer should not be modified or manipulated by C++ code once
        // its been passed to Rust.
        unsafe { absl_status_code(self.ptr) }
    }

    pub fn message(&self) -> &[u8] {
        // # Safety
        //
        // The pointer should not be modified or manipulated by C++ code once
        // its been passed to Rust
        let bv = unsafe { absl_status_message(self.ptr) };

        if bv.data().is_null() {
            &[]
        } else {
            unsafe { std::slice::from_raw_parts(bv.data(), bv.len()) }
        }
    }
}

impl Drop for AbslStatusPtr {
    fn drop(&mut self) {
        // # Safety
        //
        // The pointer should not be modified or manipulated by C++ code once
        // its been passed to Rust.
        unsafe {
            free_absl_status(self.ptr);
        }
    }
}
// See the implementations in cc/ffi/status.h
#[link(name = "status")]
unsafe extern "C" {
    fn absl_status_code(absl_status: *const AbslStatus) -> u32;
    fn absl_status_message(absl_status: *const AbslStatus) -> BytesView;
    fn free_absl_status(absl_status: *const AbslStatus);
}

#[cfg(test)]
mod test {
    use oak_ffi_bytes::BytesView;

    use super::AbslStatusPtr;

    unsafe extern "C" {
        fn create_ok_status() -> AbslStatusPtr;
        fn create_internal_error(msg: BytesView) -> AbslStatusPtr;
    }

    #[test]
    fn test_ok_status() {
        let absl_status = unsafe { create_ok_status() };

        assert_eq!(absl_status.code(), 0);
        assert_eq!(absl_status.message(), &[]);
    }

    #[test]
    fn test_err_status() {
        let absl_status =
            unsafe { create_internal_error(BytesView::new_from_slice(b"Some Error".as_slice())) };

        assert_eq!(absl_status.code(), 13);
        assert_eq!(absl_status.message(), b"Some Error");
    }
}
