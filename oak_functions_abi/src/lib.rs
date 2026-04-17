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

//! Type, constant and Wasm host function definitions for the Oak-Functions
//! application binary interface (ABI).

#![no_std]

extern crate alloc;

use alloc::vec::Vec;

/// See REQUEST_RESPONSE_ENCODING.MD in the crate root.
#[derive(Clone, PartialEq, Debug)]
pub struct Request {
    pub body: alloc::vec::Vec<u8>,
}

/// See REQUEST_RESPONSE_ENCODING.MD in the crate root.
#[derive(Clone, PartialEq, Debug)]
pub struct Response {
    pub status: StatusCode,
    /// body (may include padding 0s)
    pub body: alloc::vec::Vec<u8>,
    /// The effective length of the body, excluding any padding contained
    pub length: u64,
}

/// See REQUEST_RESPONSE_ENCODING.MD in the crate root.
#[derive(Clone, Copy, Debug, strum::Display, strum::FromRepr, PartialEq)]
#[repr(u32)]
pub enum StatusCode {
    Unspecified = 0,
    Success = 1,
    BadRequest = 2,
    PolicySizeViolation = 3,
    PolicyTimeViolation = 4,
    InternalServerError = 5,
}

// As defined in REQUEST_RESPONSE_ENCODING.MD in the crate root.
const RESPONSE_STATUS_CODE_SIZE: usize = 4;
const RESPONSE_STATUS_CODE_OFFSET: usize = 0;
static_assertions::assert_eq_size!([u8; RESPONSE_STATUS_CODE_SIZE], StatusCode);

// As defined in REQUEST_RESPONSE_ENCODING.MD in the crate root.
type ResponseLength = u64;
const RESPONSE_LENGTH_SIZE: usize = 8;
const RESPONSE_LENGTH_OFFSET: usize = RESPONSE_STATUS_CODE_SIZE;
static_assertions::assert_eq_size!([u8; RESPONSE_LENGTH_SIZE], ResponseLength);

// As defined in REQUEST_RESPONSE_ENCODING.MD in the crate root.
pub const RESPONSE_BODY_OFFSET: usize = RESPONSE_STATUS_CODE_SIZE + RESPONSE_LENGTH_SIZE;

impl Response {
    /// Creates a new instance of Response.
    ///
    /// Sets the `status` and `body` to the given status and body, and sets the
    /// `length` to the length of the body.
    pub fn create(status: StatusCode, body: Vec<u8>) -> Self {
        Response { status, body: body.clone(), length: body.len() as u64 }
    }

    /// Returns the body of the response, excluding any trailing 0s.
    ///
    /// Uses the effective length of the body, in `self.length`, to remove the
    /// trailing 0s. Returns as error if `self.length` cannot be converted
    /// to `usize` due to an overflow.
    pub fn body(&self) -> Result<&[u8], core::num::TryFromIntError> {
        let length = usize::try_from(self.length)?;
        Ok(&self.body.as_slice()[..length])
    }

    /// Creates and returns a new [`Response`] instance with the same `status`
    /// and `body` as `self`, except that the `body` may be padded, by
    /// adding a number trailing 0s, to make its length
    /// equal to `body_size`. Sets the `length` of the new instance to the
    /// length of `self.body`. Returns an error if the length of the `body`
    /// is larger than `body_size`.
    pub fn pad(&self, body_size: usize) -> anyhow::Result<Self> {
        if self.body.len() <= body_size {
            let mut body = self.body.as_slice().to_vec();
            // Set the length to the actual length of the body before padding.
            let length = body.len() as u64;
            // Add trailing 0s
            body.resize(body_size, 0);
            Ok(Response { status: self.status, body, length })
        } else {
            anyhow::bail!("response body is larger than the input body_size")
        }
    }

    pub fn encode_to_vec(&self) -> Vec<u8> {
        let mut vec: Vec<u8> =
            Vec::with_capacity(RESPONSE_LENGTH_SIZE + RESPONSE_STATUS_CODE_SIZE + self.body.len());
        vec.extend_from_slice(&(self.status as u32).to_le_bytes());
        vec.extend_from_slice(&self.length.to_le_bytes());
        vec.extend_from_slice(&self.body);
        vec
    }

    pub fn decode(bytes: &[u8]) -> anyhow::Result<Self> {
        let status: StatusCode = {
            let mut status_bytes: [u8; RESPONSE_STATUS_CODE_SIZE] = [0; RESPONSE_STATUS_CODE_SIZE];
            status_bytes.copy_from_slice(
                &bytes[RESPONSE_STATUS_CODE_OFFSET
                    ..(RESPONSE_STATUS_CODE_OFFSET + RESPONSE_STATUS_CODE_SIZE)],
            );
            StatusCode::from_repr(u32::from_le_bytes(status_bytes))
                .ok_or_else(|| anyhow::Error::msg("Invalid status code"))?
        };
        let length = {
            let mut length_bytes: [u8; RESPONSE_LENGTH_SIZE] = [0; RESPONSE_LENGTH_SIZE];
            length_bytes.copy_from_slice(
                &bytes[RESPONSE_LENGTH_OFFSET..(RESPONSE_LENGTH_OFFSET + RESPONSE_LENGTH_SIZE)],
            );
            ResponseLength::from_le_bytes(length_bytes)
        };
        let mut body: Vec<u8> =
            Vec::with_capacity(bytes.len() - RESPONSE_LENGTH_SIZE - RESPONSE_STATUS_CODE_SIZE);

        body.extend_from_slice(&bytes[RESPONSE_BODY_OFFSET..bytes.len()]);

        Ok(Self { status, body, length })
    }
}

// The Oak-Functions ABI primarily consists of a collection of Wasm host
// functions in the "oak_functions" module that are made available to
// WebAssembly modules running as Oak-Functions workloads.
// See https://rustwasm.github.io/book/reference/js-ffi.html
#[link(wasm_import_module = "oak_functions")]
unsafe extern "C" {
    /// See [`invoke`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#invoke).
    pub fn invoke(
        request_ptr: *const u8,
        request_len: usize,
        response_ptr_ptr: *mut *mut u8,
        response_len_ptr: *mut usize,
    ) -> u32;
}
