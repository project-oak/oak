//
// Copyright 2021 The Project Oak Authors
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

//! Type, constant and Wasm host function definitions for the Oak-Functions application
//! binary interface (ABI).

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.functions.abi.rs"));
    include!(concat!(env!("OUT_DIR"), "/oak.functions.lookup_data.rs"));
}

// TODO(#1963): Add tests, in an example.

// The Oak-Functions ABI primarily consists of a collection of Wasm host functions in the
// "oak_functions" module that are made available to WebAssembly modules running as Oak-Functions
// workloads.
// See https://rustwasm.github.io/book/reference/js-ffi.html
#[link(wasm_import_module = "oak_functions")]
extern "C" {
    /// Reads the user request.
    ///
    /// Stores the user request into `buf`. The size of the request data is stored into
    /// `actual_size`.
    ///
    /// If the provided space for data (`buf` plus `size`) is not large enough for the read
    /// operation, then no data will be written into `buf` and [`ErrBufferTooSmall`] will be
    /// returned. In this case, the size of the required space will be returned in the space
    /// provided by `actual_size`.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    ///
    /// Multiple calls all result in the same values in the `buf`, and return the same status.
    ///
    /// [`ErrBufferTooSmall`]: crate::OakStatus::ErrBufferTooSmall
    /// [`OakStatus`]: crate::OakStatus
    pub fn read_request(buf: *mut u8, size: usize, actual_size: *mut usize) -> u32;

    /// Writes the response.
    ///
    /// Stores `size` bytes of data from `buf` into the WebAssembly interface. This can then be
    /// returned to the user as the response.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    ///
    /// Multiple calls overwrite the response bytes in the Wasm memory.
    ///
    /// [`OakStatus`]: crate::OakStatus
    pub fn write_response(buf: *const u8, size: usize) -> u32;

    /// Retrieves a single item from the lookup data in-memory store.
    pub fn storage_get_item(
        key_buf: *const u8,
        key_size: usize,
        value_buf: *mut u8,
        value_size: usize,
        value_actual_size: *mut usize,
    ) -> u32;
}
