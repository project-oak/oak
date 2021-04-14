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

//! SDK functionality that provides idiomatic Rust wrappers around the
//! underlying Oak functions platform functionality.

use log::{debug, error};
use oak_functions_abi::OakStatus;

/// Reads and returns the user request.
///
/// This function is idempotent. Multiple call to this function all return the same value.
pub fn read_request() -> Result<Vec<u8>, OakStatus> {
    let mut buf = Vec::with_capacity(1024);
    read_request_util(&mut buf)?;
    Ok(buf)
}

/// Reads the user request into the buffer.
///
/// If the buffer does not have enough capacity, it will be reallocated with extra space so that it
/// can hold the entire request.
fn read_request_util(buf: &mut Vec<u8>) -> Result<(), OakStatus> {
    // Try reading the request twice: first with the provided vector, making
    // use of its available capacity, then with a vector whose capacity has
    // been extended to meet size requirements.
    for resized in &[false, true] {
        let mut actual_size: u32 = 0;
        let status_code = unsafe {
            oak_functions_abi::read_request(buf.as_mut_ptr(), buf.capacity(), &mut actual_size)
        };

        let status = OakStatus::from_i32(status_code as i32);
        match status {
            Some(status) => match status {
                OakStatus::Ok => {
                    unsafe {
                        // The read operation succeeded, and overwrote some fraction of the vector's
                        // available capacity with returned data (possibly zero). As the data is
                        // already present in the vector, set its length to match what's available.
                        buf.set_len(actual_size as usize);
                    }
                    return Ok(());
                }
                OakStatus::ErrBufferTooSmall if !(*resized) => {
                    // Extend the vector to be large enough for the message
                    debug!(
                        "Got space for {} bytes, need {}",
                        buf.capacity(),
                        actual_size
                    );
                    if (actual_size as usize) > buf.capacity() {
                        let extra = (actual_size as usize) - buf.len();
                        buf.reserve(extra);
                    }

                    // Try again with a buffer resized to cope with expected size of data.
                    continue;
                }
                status => {
                    return Err(status);
                }
            },
            None => return Err(OakStatus::ErrInternal),
        }
    }
    error!("unreachable code reached");
    Err(OakStatus::ErrInternal)
}

/// Write the response body.
///
/// Multiple calls to this function will replace the earlier responses. Only the last response that
/// is written will be kept and returned to the user.
pub fn write_response_body(buf: &[u8]) -> Result<(), OakStatus> {
    let status = unsafe { oak_functions_abi::write_response(buf.as_ptr(), buf.len()) };
    result_from_status(status as i32, ())
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
