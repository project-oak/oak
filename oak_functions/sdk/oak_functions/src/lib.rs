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

//! SDK functionality that provides idiomatic Rust wrappers around the underlying Oak Functions
//! platform functionality.

use oak_functions_abi::{
    proto::{Inference, OakStatus},
    ReportMetricError, ReportMetricRequest, StorageGetItemResponse, TfModelInferError,
    TfModelInferResponse,
};
use std::convert::AsRef;

/// Reads and returns the user request.
///
/// This function is idempotent. Multiple calls to this function all return the same value.
///
/// See [`read_request`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#read_request).
pub fn read_request() -> Result<Vec<u8>, OakStatus> {
    let mut buf_ptr: *mut u8 = std::ptr::null_mut();
    let mut buf_len: usize = 0;
    let status_code = unsafe { oak_functions_abi::read_request(&mut buf_ptr, &mut buf_len) };
    let status = OakStatus::from_i32(status_code as i32).ok_or(OakStatus::ErrInternal)?;
    match status {
        OakStatus::Ok => {
            let buf = from_alloc_buffer(buf_ptr, buf_len);
            Ok(buf)
        }
        status => Err(status),
    }
}

/// Write the response.
///
/// Multiple calls to this function will replace the earlier responses. Only the last response that
/// is written will be kept and returned to the user.
///
/// See [`write_response`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#write_response).
pub fn write_response(buf: &[u8]) -> Result<(), OakStatus> {
    let status = unsafe { oak_functions_abi::write_response(buf.as_ptr(), buf.len()) };
    result_from_status(status as i32, ())
}

/// Looks up an item from the in-memory lookup store.
pub fn storage_get_item(key: &[u8]) -> Result<Option<Vec<u8>>, OakStatus> {
    let response = invoke(oak_functions_abi::ExtensionHandle::LookupHandle, key)?;
    let result: StorageGetItemResponse = (&response[..]).try_into().map_err(|err| {
        log!("Failed to deserialize response: {}", err);
        OakStatus::ErrSerializing
    })?;
    Ok(result.value)
}

/// Reports an event for a count-based metrics bucket.
///
/// If differentially-private metrics are enabled in the configuration the metrics bucket totals
/// will be logged in batches after sufficient noise has been added. If events for the same bucket
/// are reported multiple times in a single request it will be counted only once.
pub fn report_event<T: AsRef<str>>(label: T) -> Result<Result<(), ReportMetricError>, OakStatus> {
    report_metric(label, 1)
}

/// Reports a metric value for a sum-based metrics bucket.
///
/// If differentially-private metrics are enabled in the configuration the metrics bucket totals
/// will be logged in batches after sufficient noise has been added. If multiple values are reported
/// for the same bucket during a single request only the last value will be used. If the reported
/// value falls outside of the configured range for the bucket, it will be clamped to the minimum or
/// maximum value.
///
/// If no values are reported for a configured bucket during a request, it will be treated as if 0
/// was reported. If the minimum value of the bucket is larger than 0 it would then be clamped to
/// the configured minimum. This could lead to unexpected bias in the results, so minimum values
/// above 0 should be used with care.
pub fn report_metric<T: AsRef<str>>(
    label: T,
    value: i64,
) -> Result<Result<(), ReportMetricError>, OakStatus> {
    let label = label.as_ref().to_owned();
    let request = ReportMetricRequest { label, value };

    let serialized_request = bincode::serialize(&request).map_err(|err| {
        log!("Failed to serialize request: {}", err);
        OakStatus::ErrSerializing
    })?;

    let serialized_response = invoke(
        oak_functions_abi::ExtensionHandle::MetricsHandle,
        &serialized_request,
    )?;

    let response: Result<(), ReportMetricError> = bincode::deserialize(&serialized_response)
        .map_err(|err| {
            log!("Failed to deserialize response: {}", err);
            OakStatus::ErrSerializing
        })?;

    Ok(response)
}

/// Writes a debug log message.
///
/// These log messages are considered sensitive, so will only be logged by the runtime if the
/// `oak_unsafe` feature is enabled.
pub fn write_log_message<T: AsRef<str>>(message: T) -> Result<(), OakStatus> {
    let buf = message.as_ref().as_bytes();
    invoke(oak_functions_abi::ExtensionHandle::LoggingHandle, buf)?;
    Ok(())
}

/// Performs inference for the given input vector with the TensorFlow model specified in the Oak
/// Functions runtime.
pub fn tf_model_infer(
    input_vector: &[u8],
) -> Result<Result<Inference, TfModelInferError>, OakStatus> {
    use prost::Message;
    let response = invoke(oak_functions_abi::ExtensionHandle::TfHandle, input_vector)?;
    let response: TfModelInferResponse = bincode::deserialize(&response).map_err(|err| {
        log!("Failed to deserialize response: {}", err);
        OakStatus::ErrSerializing
    })?;
    // We decode the inference bytes.
    let tf_result = response.result.and_then(|inference_bytes| {
        Inference::decode(&*inference_bytes).map_err(|err| {
            log!("Failed to decode: {}", err);
            TfModelInferError::ErrorDecodingInference
        })
    });
    Ok(tf_result)
}

/// Calls the testing extension with the given request. The response is directly passed on, as it is
/// decoded by the caller.
pub fn testing(request: &[u8]) -> Result<Vec<u8>, OakStatus> {
    invoke(oak_functions_abi::ExtensionHandle::TestingHandle, request)
}

// Passes the given request to the extension behind the extension handle and returns the extension's
// response.
fn invoke(
    handle: oak_functions_abi::ExtensionHandle,
    request: &[u8],
) -> Result<Vec<u8>, OakStatus> {
    let mut response_ptr: *mut u8 = std::ptr::null_mut();
    let mut response_len: usize = 0;
    let status_code = unsafe {
        oak_functions_abi::invoke(
            handle,
            request.as_ptr(),
            request.len(),
            &mut response_ptr,
            &mut response_len,
        )
    };
    let status = OakStatus::from_i32(status_code as i32).ok_or(OakStatus::ErrInternal)?;
    match status {
        OakStatus::Ok => {
            let response = from_alloc_buffer(response_ptr, response_len);
            Ok(response)
        }
        status => Err(status),
    }
}

/// Logs a debug message.
///
/// These log messages are considered sensitive, so will only be logged by the runtime if the
/// `oak_unsafe` feature is enabled.
#[macro_export]
macro_rules! log {
    ($($arg:tt)+) => {
        let _ = $crate::write_log_message(format!($($arg)+));
    }
}

/// Convert a status returned from a host function call to a `Result`.
///
/// The status is interpreted as an int representing an `OakStatus` enum value.
///
/// If the status is [`OakStatus::Ok`] then returns the provided value as [`Result::Ok`], otherwise
/// returns the status as [`Result::Err`].
///
/// Note that host function calls usually return an `u32` because of limitations of the Wasm type
/// system, so these values would usually be converted (via a cast) to `i32` by callers.
pub fn result_from_status<T>(status: i32, val: T) -> Result<T, OakStatus> {
    match OakStatus::from_i32(status) {
        Some(OakStatus::Ok) => Ok(val),
        Some(status) => Err(status),
        None => Err(OakStatus::Unspecified),
    }
}

#[no_mangle]
pub extern "C" fn alloc(len: u32) -> *mut u8 {
    // Create a new mutable buffer with capacity `len`.
    let mut buf = Vec::with_capacity(len as usize);
    let ptr = buf.as_mut_ptr();
    // Take ownership of the buffer and ensure that it is not freed at the end of this function.
    std::mem::forget(buf);
    // Return the pointer so the runtime can write data at this address.
    ptr
}

/// Convenience method to reconstruct an owned `Vec<u8>` from the raw parts (address and size)
/// returned as part of an ABI method invocation that relies on the `alloc` method to allocate the
/// buffer.
fn from_alloc_buffer(buf_ptr: *mut u8, buf_len: usize) -> Vec<u8> {
    unsafe { Vec::from_raw_parts(buf_ptr, buf_len, buf_len) }
}
