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
use serde::{Deserialize, Serialize};

pub mod utils;

#[derive(Debug)]
pub enum ClientError {
    InvalidRequest,
    InvalidResponse,
    TransportError(TransportError),
}

impl From<TransportError> for ClientError {
    fn from(e: TransportError) -> Self {
        ClientError::TransportError(e)
    }
}

#[derive(Debug)]
pub enum TransportError {
    InvalidMessage,
    InvalidTransactionId,
    InvalidMethodId,
}

/// Unique identifier of a method within a service.
type MethodId = u32;

/// Header of a transactional message.
///
/// See <https://fuchsia.dev/fuchsia-src/reference/fidl/language/wire-format#transactional-messages>
#[derive(Serialize, Deserialize)]
pub struct Header {
    /// Identifies the transaction over the underlying transport. Each transaction (a.k.a. call or
    /// invocation) over the same transport must have a unique transaction id (regardless of the
    /// method_id value).
    ///
    /// The client picks a unique transaction id to put in the request header, and when the server
    /// replies to that message, it also uses the same transaction id in the response message.
    pub transaction_id: u32,

    /// Identifies the method to be invoked, as defined by the IDL.
    pub method_id: MethodId,
}

/// A transactional message.
///
/// The body field contains the serialized payload of the request or response.
///
/// Note that the serialization of the body does not have to match the serialization of the Message
/// itself. For instance, the Message may be serialized via bincode, but the payload may be
/// serialized via protobuf.
#[derive(Serialize, Deserialize)]
pub struct TransportMessage {
    pub header: Header,
    pub body: Vec<u8>,
}

/// A message-oriented transport that allows performing invocations.
///
/// Implementations of this trait are responsible for assigning a unique transaction id for each
/// invocation request, and checking whether the transaction id on the response matches that of the
/// request.
pub trait Transport {
    fn invoke(
        &mut self,
        request_message: TransportMessage,
    ) -> Result<TransportMessage, TransportError>;
}

/// A wrapper for a message-oriented channel handle, which implements the [`Transport`] trait.
struct Channel {
    handle: u32,
    next_transaction_id: u32,
}

impl Channel {
    #[allow(dead_code)]
    pub fn new(handle: u32) -> Self {
        Self {
            handle,
            next_transaction_id: 0,
        }
    }
}

impl Transport for Channel {
    fn invoke(
        &mut self,
        request_message: TransportMessage,
    ) -> Result<TransportMessage, TransportError> {
        let transaction_id = self.next_transaction_id;
        self.next_transaction_id += 1;
        let mut request_message = request_message;
        request_message.header.transaction_id = transaction_id;
        // The serialization of the outer message is fixed by the transport, since the header needs
        // to be deserializable by the other end of the transport, but the body of the
        // request / response is serialized at a higher level, and in potentially different format,
        // since that's handled by the application (client and server).
        let request_bytes =
            bincode::serialize(&request_message).map_err(|_| TransportError::InvalidMessage)?;
        let response_bytes = invoke(self.handle, &request_bytes)?;
        let response_message: TransportMessage =
            bincode::deserialize(&response_bytes).map_err(|_| TransportError::InvalidMessage)?;

        if response_message.header.transaction_id != transaction_id {
            return Err(TransportError::InvalidTransactionId);
        }

        Ok(response_message)
    }
}

/// A low-level message-oriented transport over channels. This is meant to emulate the low-level
/// Wasm ABI in Oak, and will eventually be replaced by that.
fn invoke(_channel_handle: u32, _request: &[u8]) -> Result<Vec<u8>, TransportError> {
    unimplemented!()
}
