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

use alloc::vec::Vec;
use core::fmt::Debug;

pub mod utils;

#[derive(Debug)]
pub enum Error {
    /// The request message could not be deserialized correctly.
    InvalidRequest,
    /// The response message could not be deserialized correctly.
    InvalidResponse,
    /// The method id provided for the invocation was not implemented by the server.
    InvalidMethodId,
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
