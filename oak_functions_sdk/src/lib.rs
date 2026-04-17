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

#![no_std]
#![feature(never_type)]
#![feature(result_flattening)]
#![doc = core::include_str!("../README.md")]

extern crate alloc;

use alloc::{string::ToString, vec::Vec};
use core::ops::Deref;

use micro_rpc::{Status, StatusCode};
use oak_micro_rpc::oak::functions::wasm::v1::StdWasmApiClient;
use oak_proto_rust::oak::functions::wasm::v1::{
    BytesValue, LogRequest, LogResponse, LookupDataMultiRequest, LookupDataMultiResponse,
    LookupDataRequest, LookupDataResponse, ReadRequestRequest, ReadRequestResponse, TestRequest,
    TestResponse, WriteResponseRequest, WriteResponseResponse,
};

/// See [`StdWasmApiClient::read_request`].
pub fn read_request() -> Result<Vec<u8>, Status> {
    client().read_request(&ReadRequestRequest {}).flatten().map(|ReadRequestResponse { body }| body)
}

/// See [`StdWasmApiClient::write_response`].
pub fn write_response(buf: &[u8]) -> Result<(), Status> {
    client()
        .write_response(&WriteResponseRequest { body: buf.to_vec() })
        .flatten()
        .map(|WriteResponseResponse {}| ())
}

/// See [`StdWasmApiClient::lookup_data`].
pub fn storage_get_item(key: &[u8]) -> Result<Option<Vec<u8>>, Status> {
    client()
        .lookup_data(&LookupDataRequest { key: key.to_vec() })
        .flatten()
        .map(|LookupDataResponse { value }| value)
}

/// See [`StdWasmApiClient::lookup_data_multi`].
pub fn storage_get_items<T>(keys: T) -> Result<Vec<Option<Vec<u8>>>, Status>
where
    T: IntoIterator,
    T::Item: Deref,
    <T::Item as Deref>::Target: AsRef<[u8]>,
{
    client()
        .lookup_data_multi(&LookupDataMultiRequest {
            keys: keys.into_iter().map(|key| key.as_ref().to_vec()).collect(),
        })
        .flatten()
        .map(|LookupDataMultiResponse { values }| {
            values.into_iter().map(bytes_value_to_option).collect()
        })
}

fn bytes_value_to_option(b: BytesValue) -> Option<Vec<u8>> {
    if b.found { Some(b.value) } else { None }
}

/// See [`StdWasmApiClient::log`].
pub fn write_log_message<T: AsRef<str>>(message: T) -> Result<(), Status> {
    client()
        .log(&LogRequest { message: message.as_ref().to_string() })
        .flatten()
        .map(|LogResponse {}| ())
}

/// See [`StdWasmApiClient::test`].
pub fn testing(request: &[u8], echo: bool) -> Result<Vec<u8>, Status> {
    client()
        .test(&TestRequest { body: request.to_vec(), echo })
        .flatten()
        .map(|TestResponse { body }| body)
}

/// See [`invoke`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#invoke).
fn invoke(request: &[u8]) -> Result<Vec<u8>, Status> {
    let mut response_ptr: *mut u8 = core::ptr::null_mut();
    let mut response_len: usize = 0;
    let status_code = unsafe {
        oak_functions_abi::invoke(
            request.as_ptr(),
            request.len(),
            &mut response_ptr,
            &mut response_len,
        )
    };
    let status_code: StatusCode = status_code.into();
    match status_code {
        StatusCode::Ok => {
            let response = from_alloc_buffer(response_ptr, response_len);
            Ok(response)
        }
        status_code => Err(Status::new(status_code)),
    }
}

/// Logs a debug message.
///
/// These log messages are considered sensitive, so will only be logged by the
/// runtime if the `oak_unsafe` feature is enabled.
#[macro_export]
macro_rules! log {
    ($($arg:tt)+) => {
        let _ = $crate::write_log_message(format!($($arg)+));
    }
}

/// A wrapper around the `invoke` function that implements the
/// [`micro_rpc::Transport`] trait.
///
/// This object is stateless, so it can be created and discarded for each
/// invocation.
struct Transport;

impl micro_rpc::Transport for Transport {
    type Error = Status;

    fn invoke(&mut self, request_bytes: &[u8]) -> Result<Vec<u8>, Self::Error> {
        invoke(request_bytes)
    }
}

/// Creates a new client for the Oak Functions ABI.
fn client() -> StdWasmApiClient<Transport> {
    StdWasmApiClient::new(Transport)
}

#[unsafe(no_mangle)]
pub extern "C" fn alloc(len: u32) -> *mut u8 {
    // Create a new mutable buffer with capacity `len`.
    let mut buf = Vec::with_capacity(len as usize);
    let ptr = buf.as_mut_ptr();
    // Take ownership of the buffer and ensure that it is not freed at the end of
    // this function.
    core::mem::forget(buf);
    // Return the pointer so the runtime can write data at this address.
    ptr
}

/// Convenience method to reconstruct an owned `Vec<u8>` from the raw parts
/// (address and size) returned as part of an ABI method invocation that relies
/// on the `alloc` method to allocate the buffer.
fn from_alloc_buffer(buf_ptr: *mut u8, buf_len: usize) -> Vec<u8> {
    unsafe { Vec::from_raw_parts(buf_ptr, buf_len, buf_len) }
}
