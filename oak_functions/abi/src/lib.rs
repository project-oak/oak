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

use crate::proto::{ChannelHandle, ChannelStatus};

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.functions.abi.rs"));
    include!(concat!(env!("OUT_DIR"), "/oak.functions.lookup_data.rs"));
    include!(concat!(env!("OUT_DIR"), "/oak.functions.invocation.rs"));

    impl Response {
        /// Creates a new instance of Response.
        ///
        /// Sets the `status` and `body` to the given status and body, and sets the
        /// `length` to the length of the body.
        pub fn create(status: StatusCode, body: Vec<u8>) -> Self {
            Response {
                status: status as i32,
                body: body.clone(),
                length: body.len() as u64,
            }
        }

        /// Returns the body of the response, excluding any trailing 0s.
        ///
        /// Uses the effective length of the body, in `self.length`, to remove the trailing 0s.
        /// Returns as error if `self.length` cannot be converted to `usize` due to an overflow.
        pub fn body(&self) -> Result<&[u8], std::num::TryFromIntError> {
            use std::convert::TryFrom;

            let length = usize::try_from(self.length)?;
            Ok(&self.body.as_slice()[..length])
        }
    }
}

// TODO(#1963): Add tests, in an example.

// The Oak-Functions ABI primarily consists of a collection of Wasm host functions in the
// "oak_functions" module that are made available to WebAssembly modules running as Oak-Functions
// workloads.
// See https://rustwasm.github.io/book/reference/js-ffi.html
#[link(wasm_import_module = "oak_functions")]
extern "C" {
    /// See [`read_request`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#read_request).
    pub fn read_request(buf_ptr_ptr: *mut *mut u8, buf_len_ptr: *mut usize) -> u32;

    /// See [`write_response`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#write_response).
    pub fn write_response(buf_ptr: *const u8, buf_len: usize) -> u32;

    /// See [`write_log_message`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#write_log_message).
    pub fn write_log_message(buf_ptr: *const u8, buf_len: usize) -> u32;

    /// See [`report_metric`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#report_metric).
    pub fn report_metric(buf_ptr: *const u8, buf_len: usize, value: i64) -> u32;

    /// See [`storage_get_item`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#storage_get_item).
    pub fn storage_get_item(
        key_ptr: *const u8,
        key_len: usize,
        value_ptr_ptr: *mut *mut u8,
        value_len_ptr: *mut usize,
    ) -> u32;

    /// See [`tf_model_infer`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#tf_model_infer).
    pub fn tf_model_infer(
        input_ptr: *const u8,
        input_len: usize,
        inference_ptr_ptr: *mut *mut u8,
        inference_len_ptr: *mut usize,
    ) -> u32;

    /// Allocates a buffer on the callers memory to write a message from the channel with
    /// `channel_handle`. After a successful call `dest_buf_ptr_ptr` holds the address of the
    /// buffer and `dest_buf_len_ptr` holds its length. The caller can then read
    /// the message from `dest_buf_ptr_ptr`.
    ///
    /// Returns a status code to indicate success. In particular, returns immediately
    /// with an appropriate status code, if no message is available on the channel.
    pub fn channel_read(
        channel_handle: ChannelHandle,
        dest_buf_ptr_ptr: *mut *mut u8,
        dest_buf_len_ptr: *mut usize,
    ) -> ChannelStatus;

    /// Writes a message, i.e., `src_buf_len` bytes, from `scr_buf_ptr` into the channel with
    /// `channel_handle`.
    ///
    /// Returns a status code to indicate success.
    pub fn channel_write(
        channel_handle: ChannelHandle,
        src_buf_ptr: *const u8,
        src_buf_len: usize,
    ) -> ChannelStatus;

    /// Waits until at least one of the channels from the channel handles in the buffer at
    /// `channel_handle_buf_ptr` has a message to read, or
    /// until the `deadline_ms` expires. After a successful call to `channel_wait`, the buffer at
    /// `ready_channel_handle_buf_ptr` holds the channel handles with at least one message to read.
    /// Both, `channel_handle_buf_len` and `ready_channel_handle_buf_len` hold the length of the
    /// respective buffers in bytes.
    ///
    /// Returns a status code to indicate success or deadline expiration.
    pub fn channel_wait(
        channel_handle_buf_ptr: *const ChannelHandle,
        channel_handle_buf_len: usize,
        ready_channel_handle_buf_ptr: *mut *mut i32,
        ready_channel_handle_buf_len: *mut usize,
        deadline_ms: u32,
    ) -> ChannelStatus;
}
