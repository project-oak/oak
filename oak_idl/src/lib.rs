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

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

use crate::alloc::string::ToString;
use alloc::{string::String, vec::Vec};
use core::fmt::Debug;

pub mod utils;

#[derive(Debug)]
pub struct Status {
    pub code: StatusCode,
    /// English message that helps developers understand and resolve the error.
    pub message: String,
}

impl Status {
    pub fn new(code: StatusCode) -> Self {
        Self {
            code,
            message: "".to_string(),
        }
    }

    pub fn new_with_message(code: StatusCode, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
        }
    }
}

/// gRPC status codes used by [`Status`].
///
/// These variants match the [gRPC status codes].
///
/// [gRPC status codes]: https://github.com/grpc/grpc/blob/master/doc/statuscodes.md#status-codes-and-their-use-in-grpc
// Based on tonic's status code struct: https://github.com/hyperium/tonic/blob/91b73f9fc3c1bc281e85177808721b3efe37ece0/tonic/src/status.rs
#[derive(Debug)]
pub enum StatusCode {
    /// The operation completed successfully.
    Ok = 0,

    /// The operation was cancelled.
    Cancelled = 1,

    /// Unknown error.
    Unknown = 2,

    /// Client specified an invalid argument.
    InvalidArgument = 3,

    /// Deadline expired before operation could complete.
    DeadlineExceeded = 4,

    /// Some requested entity was not found.
    NotFound = 5,

    /// Some entity that we attempted to create already exists.
    AlreadyExists = 6,

    /// The caller does not have permission to execute the specified operation.
    PermissionDenied = 7,

    /// Some resource has been exhausted.
    ResourceExhausted = 8,

    /// The system is not in a state required for the operation's execution.
    FailedPrecondition = 9,

    /// The operation was aborted.
    Aborted = 10,

    /// Operation was attempted past the valid range.
    OutOfRange = 11,

    /// Operation is not implemented or not supported.
    Unimplemented = 12,

    /// Internal error.
    Internal = 13,

    /// The service is currently unavailable.
    Unavailable = 14,

    /// Unrecoverable data loss or corruption.
    DataLoss = 15,

    /// The request does not have valid authentication credentials
    Unauthenticated = 16,
}

impl From<u32> for StatusCode {
    fn from(i: u32) -> Self {
        match i {
            0 => StatusCode::Ok,
            1 => StatusCode::Cancelled,
            2 => StatusCode::Unknown,
            3 => StatusCode::InvalidArgument,
            4 => StatusCode::DeadlineExceeded,
            5 => StatusCode::NotFound,
            6 => StatusCode::AlreadyExists,
            7 => StatusCode::PermissionDenied,
            8 => StatusCode::ResourceExhausted,
            9 => StatusCode::FailedPrecondition,
            10 => StatusCode::Aborted,
            11 => StatusCode::OutOfRange,
            12 => StatusCode::Unimplemented,
            13 => StatusCode::Internal,
            14 => StatusCode::Unavailable,
            15 => StatusCode::DataLoss,
            16 => StatusCode::Unauthenticated,

            _ => StatusCode::Unknown,
        }
    }
}

impl From<StatusCode> for u32 {
    fn from(code: StatusCode) -> u32 {
        code as u32
    }
}

/// Unique identifier of a method within a service.
type MethodId = u32;

/// A request message representing an invocation of the method identified by `method_id` with the
/// argument serialized as `body`.
pub struct Request {
    /// Identifies the method to be invoked, as defined by the IDL.
    pub method_id: MethodId,
    /// The serialized request payload, corresponding to the argument of the method identified by
    /// `method_id`.
    pub body: Vec<u8>,
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
    fn invoke(&mut self, request: Request) -> Result<Vec<u8>, Status>;
}

/// Async version of [`Handler`] to support async clients.
#[cfg(feature = "async-clients")]
#[async_trait::async_trait]
pub trait AsyncHandler {
    async fn invoke(&mut self, request: Request) -> Result<Vec<u8>, Status>;
}
