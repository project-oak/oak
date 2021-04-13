//
// Copyright 2019 The Project Oak Authors
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

// Reads and returns the user request.
pub fn read_request_body() -> Result<Vec<u8>, OakStatus> {
    let mut buf = Vec::with_capacity(1024);
    read_request(&mut buf)?;
    Ok(buf)
}

/// Reads the user request into the buffer.
/// If the buffer does not have enough capacity, it will be reallocated with extra space so that it
/// can hold the entire request.
fn read_request(buf: &mut Vec<u8>) -> Result<(), OakStatus> {
    // Try reading the request twice: first with provided vectors, making
    // use of their available capacity, then with vectors whose capacity has
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
pub fn write_response_body(response_body: &str) -> Result<(), OakStatus> {
    write_response(response_body.as_bytes())
}

fn write_response(buf: &[u8]) -> Result<(), OakStatus> {
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

/// Install a panic hook that logs [panic information].
///
/// Logs panic information to the logging channel, if one is set.
///
/// [panic information]: std::panic::PanicInfo
// This is copied from oak sdk: sdk/rust/oak/src/lib.rs
pub fn set_panic_hook() {
    std::panic::set_hook(Box::new(|panic_info| {
        let payload = panic_info.payload();
        // The payload can be a static string slice or a string, depending on how panic was called.
        // Code for extracting the message is inspired by the rust default panic hook:
        // https://github.com/rust-lang/rust/blob/master/src/libstd/panicking.rs#L188-L194
        let msg = match payload.downcast_ref::<&'static str>() {
            Some(content) => *content,
            None => match payload.downcast_ref::<String>() {
                Some(content) => content.as_ref(),
                None => "<UNKNOWN MESSAGE>",
            },
        };
        let (file, line) = match panic_info.location() {
            Some(location) => (location.file(), location.line()),
            None => ("<UNKNOWN FILE>", 0),
        };
        error!(
            "panic occurred in file '{}' at line {}: {}",
            file, line, msg
        );
    }));
}
