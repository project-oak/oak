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

pub use crate::proto::ExtensionHandle;
use serde_derive::{Deserialize, Serialize};

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
            let length = usize::try_from(self.length)?;
            Ok(&self.body.as_slice()[..length])
        }
    }
}

/// Holds the `label` and the `value` to report a metric.
#[derive(Serialize, Deserialize)]
#[cfg(feature = "oak-metrics")]
pub struct ReportMetricRequest {
    pub label: String,
    pub value: i64,
}

#[derive(Serialize, Deserialize, Debug)]
#[cfg(feature = "oak-tf")]
pub enum TfModelInferError {
    // Error when running the TensorFlow model, due to bad input tensor.
    BadTensorFlowModelInput,
    // Error when decoding the inference bytes.
    ErrorDecodingInference,
}

#[derive(Serialize, Deserialize)]
#[cfg(feature = "oak-tf")]
pub struct TfModelInferResponse {
    pub result: Result<Vec<u8>, TfModelInferError>,
}

#[derive(Serialize, Deserialize)]
pub enum TestingRequest {
    Echo(String),
    Blackhole(String),
}

#[derive(Serialize, Deserialize)]
pub enum TestingResponse {
    Echo(String),
}

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
    pub fn report_metric(buf_ptr: *const u8, buf_len: usize) -> u32;

    /// See [`storage_get_item`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#storage_get_item).
    pub fn storage_get_item(
        key_ptr: *const u8,
        key_len: usize,
        value_ptr_ptr: *mut *mut u8,
        value_len_ptr: *mut usize,
    ) -> u32;

    /// See [`invoke`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#invoke).
    pub fn invoke(
        handle: ExtensionHandle,
        request_ptr: *const u8,
        request_len: usize,
        response_ptr_ptr: *mut *mut u8,
        response_len_ptr: *mut usize,
    ) -> u32;
}
