//
// Copyright 2024 The Project Oak Authors
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

use oak_ffi_bytes::{RustBytes, free_rust_bytes_contents};

/// A simple type representing an error. It contains only a message, containing
/// a stringified representation of a Rust error.
#[repr(C)]
pub struct Error {
    message: RustBytes,
}

impl Error {
    /// Create a new instance containing the provided [`message`].
    pub fn new(message: impl std::fmt::Display) -> Error {
        Error {
            message: RustBytes::new(format!("{message:#}").as_bytes().to_vec().into_boxed_slice()),
        }
    }

    pub fn new_raw(message: impl std::fmt::Display) -> *mut Error {
        Box::into_raw(Box::new(Error::new(message)))
    }

    pub fn message(&self) -> &RustBytes {
        &self.message
    }
}

/// A type that will contain *either* a result (RustBytes) type, or an error
/// type.
///
/// It's suggested to follow this pattern when creating new fallible return
/// types.
#[repr(C)]
pub struct ErrorOrRustBytes {
    pub result: *const RustBytes,
    pub error: *const Error,
}

impl ErrorOrRustBytes {
    /// Create a new instance with the `error` field populated with a newly
    /// created Error instance.
    pub fn err(msg: impl std::fmt::Display) -> ErrorOrRustBytes {
        ErrorOrRustBytes { result: std::ptr::null_mut(), error: Error::new_raw(msg) }
    }

    /// Create a sucessful result with the provided bytes.
    ///
    /// Ownership of the bytes will be passed to this instance.
    pub fn ok(bytes: Box<[u8]>) -> ErrorOrRustBytes {
        ErrorOrRustBytes {
            result: Box::into_raw(Box::new(RustBytes::new(bytes))),
            error: std::ptr::null_mut(),
        }
    }

    /// Create a null result.
    pub fn null() -> ErrorOrRustBytes {
        ErrorOrRustBytes { result: std::ptr::null_mut(), error: std::ptr::null_mut() }
    }

    /// Return the result [`RustBytes`] as a slice. No ownership changes.
    ///
    /// # Safety
    ///
    /// The `result` field contains a non-null, valid, aligned pointer to a
    /// valid [`RustBytes`] instance.
    pub unsafe fn result_slice(&self) -> &[u8] {
        unsafe { (*self.result).as_slice() }
    }
}

///  Return ownership of the [`Error`] pointer to Rust, where it will be
///  dropped and all related memory released.
///
///  # Safety
///
///  * The provided [`Error`] pointer is non-null, valid, and properly aligned.
///  * The [`Bytes`] representing the error message is valid.
///  * The pointer should not be used anymore after calling this function.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn free_error(error: *const Error) {
    unsafe {
        free_rust_bytes_contents((*error).message);
        drop(Box::from_raw(error as *mut Error));
    }
}
