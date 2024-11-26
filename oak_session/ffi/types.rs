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

/// A basic wrapper around C-provided bytes of known length.
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Bytes {
    data: *const u8,
    len: usize,
}

impl Bytes {
    /// Create a new [`Bytes`] instance from the provided [`Box<[u8]>`].
    /// Ownership of the box will be released, so the memory will need
    /// to be freed later with a call to [`free_bytes`].
    pub fn new(bytes: Box<[u8]>) -> Bytes {
        let leaked_bytes = Box::leak(bytes);
        Bytes { data: leaked_bytes.as_ptr(), len: leaked_bytes.len() }
    }

    /// Create a new [`Bytes`] by allocating a new [`Box<[u8]`>] with a copy of
    /// the provided slice data.
    /// Ownership of the box will be released, so the memory will need to be
    /// freed later with a call to [`free_bytes`].
    pub fn new_alloc(bytes: &[u8]) -> Bytes {
        Self::new(bytes.to_vec().into_boxed_slice())
    }

    /// Return a `std::slice` representation of this [`Bytes`] instance. There
    /// will not be any ownership changes.
    ///
    /// # Safety
    /// The instance contains a non-null, properly aligned, valid pointer.
    pub unsafe fn as_slice(&self) -> &[u8] {
        std::slice::from_raw_parts(self.data, self.len)
    }
}

/// A simple type representing an error. It contains only a message, containing
/// a stringified representation of a Rust error.
#[repr(C)]
pub struct Error {
    message: Bytes,
}

impl Error {
    /// Create a new instance containing the provided [`message`].
    pub fn new(message: impl AsRef<str>) -> Error {
        Error { message: Bytes::new_alloc(message.as_ref().as_bytes()) }
    }

    pub fn new_raw(message: impl AsRef<str>) -> *const Error {
        Box::into_raw(Box::new(Error::new(message)))
    }
}

/// A type that will contain *either* a result (Bytes) type, or an error type.
#[repr(C)]
pub struct ErrorOrBytes {
    pub result: *const Bytes,
    pub error: *const Error,
}

impl ErrorOrBytes {
    /// Create a new instance with the `error` field populated with a newly
    /// created Error instance.
    pub fn err(msg: impl AsRef<str>) -> ErrorOrBytes {
        ErrorOrBytes { result: std::ptr::null(), error: Error::new_raw(msg) }
    }

    pub fn ok(bytes: &[u8]) -> ErrorOrBytes {
        ErrorOrBytes {
            result: Box::into_raw(Box::new(Bytes::new_alloc(bytes))),
            error: std::ptr::null(),
        }
    }

    pub fn null() -> ErrorOrBytes {
        ErrorOrBytes { result: std::ptr::null(), error: std::ptr::null() }
    }

    /// Return the result [`Bytes`] as a slice. No ownership changes.
    ///
    /// # Safety
    ///
    /// The `result` field contains a non-null, valid, aligned pointer to a
    /// valid [`Bytes`] instance.
    pub unsafe fn result_slice(&self) -> &[u8] {
        (*self.result).as_slice()
    }
}

///  Return ownership of memory owned by the [`Bytes`] instance to Rust, where
/// it will be  dropped and all related memory released.
///
///  # Safety
///
///  * The provided [`Bytes`] is a valid, still allocated instance.
///  * The instance should not be used anymore after calling this function.
#[no_mangle]
pub unsafe extern "C" fn free_bytes(bytes: Bytes) {
    drop(Box::from_raw(std::slice::from_raw_parts_mut(bytes.data as *mut u8, bytes.len)))
}

///  Return ownership of the [`Error`] pointer to Rust, where it will be
///  dropped and all related memory released.
///
///  # Safety
///
///  * The provided [`Error`] pointer is non-null, valid, and properly aligned.
///  * The [`Bytes`] representing the error message is valid.
///  * The pointer should not be used anymore after calling this function.
#[no_mangle]
pub unsafe extern "C" fn free_error(error: *mut Error) {
    drop(Box::from_raw(error));
}
