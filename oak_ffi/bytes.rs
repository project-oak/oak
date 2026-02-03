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

/// A basic wrapper around Rust or C-provided bytes of known length.
///
/// This structure can be passed back and forth between Rust and C code.
/// Functions that use the type should explain the lifetime expectations for the
/// type.
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct BytesView {
    data: *const u8,
    len: usize,
}

impl BytesView {
    /// Create a new instance wrapping the provided data of the specified
    /// length.
    pub fn new(data: *const u8, len: usize) -> BytesView {
        BytesView { data, len }
    }

    /// Create a new instance wrapping the provided slice.
    pub fn new_from_slice(slice: &[u8]) -> BytesView {
        if slice.is_empty() {
            // Empty slices return 0x1 for their ptr value.
            BytesView::new(core::ptr::null(), 0)
        } else {
            BytesView::new(slice.as_ptr(), slice.len())
        }
    }

    /// Return a `std::slice` representation of this [`BytesView`] instance.
    /// There will not be any ownership changes.
    ///
    /// # Safety
    /// The instance contains a non-null, properly aligned, valid pointer.
    pub unsafe fn as_slice(&self) -> &[u8] {
        if self.data.is_null() {
            &[]
        } else {
            unsafe { std::slice::from_raw_parts(self.data, self.len) }
        }
    }

    pub fn data(&self) -> *const u8 {
        self.data
    }
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

/// A basic wrapper around Rust-provided bytes of known length.
///
/// Rust code can use this to pass Rust-owned data back to C.
/// C code is responsible for releasing the bytes using `free_rust_bytes`.
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct RustBytes {
    data: *const u8,
    len: usize,
}

impl RustBytes {
    /// Create a new [`RustBytes`] instance from the provided [`Box<[u8]>`].
    /// Ownership of the box will be released, so the memory will need
    /// to be freed later with a call to [`free_rust_bytes`].
    pub fn new(bytes: Box<[u8]>) -> RustBytes {
        let raw_bytes_ptr = Box::into_raw(bytes);
        if raw_bytes_ptr.is_empty() {
            // Empty slices will return 0x01 for the pointer, so we need to make sure
            // that C still gets a null pointer.
            RustBytes { data: core::ptr::null(), len: 0 }
        } else {
            RustBytes { data: raw_bytes_ptr as *const u8, len: raw_bytes_ptr.len() }
        }
    }

    /// Return a `std::slice` representation of this [`RustBytes`] instance.
    /// There will not be any ownership changes.
    ///
    /// # Safety
    /// The instance contains a non-null, properly aligned, valid pointer.
    pub unsafe fn as_slice(&self) -> &[u8] {
        // Empty slices will return 0x01 for the pointer, so we need to make sure
        // that C still gets a null pointer.
        if self.data.is_null() {
            &[]
        } else {
            unsafe { std::slice::from_raw_parts(self.data, self.len) }
        }
    }

    /// Return a [`BytesView`] containing the Rust bytes.
    pub fn as_bytes_view(&self) -> BytesView {
        if self.data.is_null() {
            // Empty slices will return 0x01 for the pointer, so we need to make sure
            // that C still gets a null pointer.
            BytesView::new(std::ptr::null(), 0)
        } else {
            BytesView::new(self.data, self.len)
        }
    }
}

///  Return ownership of the [`RustBytes`] pointer back to Rust, where
/// it will be  dropped and all related memory released, including the allocated
/// contents.
///
/// Note: if you have a [`RustBytes`] structure, but not a poiner to it, use
/// [`free_rust_bytes_contents`]` instead.
///
/// # Safety
///
///  * The provided [`Bytes`] is a valid, still allocated instance, containing
///    valid, allocated bytes.
///  * The instance should not be used anymore after calling this function.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn free_rust_bytes(bytes: *const RustBytes) {
    let bytes_boxed = unsafe { Box::from_raw(bytes as *mut RustBytes) };
    unsafe {
        free_rust_bytes_contents(*bytes_boxed);
    }
    drop(bytes_boxed)
}

/// Release the rust memory owned by the provided Bytes struct.
///
/// # Safety
///
///  * The provided [`Bytes`] is a valid, still allocated instance, containing
///    valid, allocated bytes. It should not be used anymore after calling this
///    function.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn free_rust_bytes_contents(bytes: RustBytes) {
    if bytes.data.is_null() {
        return;
    }
    drop(unsafe { Box::from_raw(std::slice::from_raw_parts_mut(bytes.data as *mut u8, bytes.len)) })
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn empty_rust_bytes() {
        unsafe {
            let data = Box::new([]);
            let bytes: *const RustBytes = Box::into_raw(Box::new(RustBytes::new(data)));
            free_rust_bytes(bytes);
        }
    }

    #[test]
    fn rust_bytes() {
        unsafe {
            let data = Box::new([1, 2, 3]);
            let bytes: *const RustBytes = Box::into_raw(Box::new(RustBytes::new(data)));
            free_rust_bytes(bytes);
        }
    }
}
