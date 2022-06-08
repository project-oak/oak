//
// Copyright 2022 The Project Oak Authors
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

extern crate alloc;

use alloc::{string::String, vec::Vec};
use core::fmt::Debug;

pub mod utils;

// TODO(#2500): Align with gRPC Status.
// Ref: https://github.com/grpc/grpc/blob/master/src/proto/grpc/status/status.proto
/// Logical error model.
#[derive(Debug)]
pub struct Error {
    pub code: ErrorCode,
    /// English message that helps developers understand and resolve the error.
    pub message: Option<String>,
}

// TODO(#2500): Align these with gRPC status codes.
/// Basic error code to categorize the error. Error codes are represented as an
/// u32 id. The id `0` is reserved, as it may be used to indicate an "Ok" status
/// in transport implementations.
#[repr(u32)]
#[derive(Debug)]
pub enum ErrorCode {
    /// The request message could not be deserialized correctly.
    InvalidRequest = 1,
    /// The response message could not be deserialized correctly.
    InvalidResponse = 2,
    /// The method id provided for the invocation was not implemented by the server.
    InvalidMethodId = 3,
    /// The request was deserialized correctly but contained invalid values.
    BadRequest = 4,
    /// An error occured while invoking the method on the server.
    InternalError = 5,
    /// Unknown error.
    Unknown = 6,
}

impl From<u32> for ErrorCode {
    fn from(i: u32) -> Self {
        match i {
            1 => ErrorCode::InvalidRequest,
            2 => ErrorCode::InvalidResponse,
            3 => ErrorCode::InvalidMethodId,
            4 => ErrorCode::BadRequest,
            5 => ErrorCode::InternalError,
            6 => ErrorCode::Unknown,

            _ => ErrorCode::Unknown,
        }
    }
}

impl From<ErrorCode> for u32 {
    fn from(code: ErrorCode) -> u32 {
        code as u32
    }
}

/// Unique identifier of a method within a service.
type MethodId = u32;

/// A request message representing an invocation of the method identified by `method_id` with the
/// argument serialized as `body`.
pub struct Request<'a> {
    /// Identifies the method to be invoked, as defined by the IDL.
    pub method_id: MethodId,
    /// The serialized request payload, corresponding to the argument of the method identified by
    /// `method_id`.
    pub body: &'a [u8],
}

/// A message-oriented handler that allows performing invocations.
///
/// The asymmetry between the request and response types is due to the fact that a [`Request`]
/// instance contains a reference to the request body buffer, and also contains the method id of the
/// invocation, while the return value is a `Vec<u8>` since it is allocated and owned by the
/// invocation handler.
///
/// This is conceptually similar to a method that takes `&[u8]` as input but returns `Vec<u8>` as
/// output.
pub trait Handler {
    fn invoke(&mut self, request: Request) -> Result<Vec<u8>, Error>;
}
