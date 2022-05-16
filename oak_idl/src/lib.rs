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

use serde::{Deserialize, Serialize};
use std::{
    fmt::Debug,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

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

/// A helper struct to facilitate building a [`Message`].
///
/// It delegates most methods to the underlying [`flatbuffers::FlatBufferBuilder`] instance, but it
/// adds a [`MessageBuilder::finish`] method that returns a completed [`Message`] instance.
///
/// ```
/// # struct Foo;
/// #
/// # impl flatbuffers::Verifiable for Foo {
/// #     fn run_verifier(
/// #         v: &mut flatbuffers::Verifier,
/// #         pos: usize,
/// #     ) -> Result<(), flatbuffers::InvalidFlatbuffer> {
/// #         Ok(())
/// #     }
/// # }
/// #
/// # impl<'a> flatbuffers::Follow<'a> for Foo {
/// #     type Inner = Self;
/// #     fn follow(buf: &'a [u8], log: usize) -> Self::Inner {
/// #         Self
/// #     }
/// # }
/// #
/// # impl Foo {
/// #     pub fn create(b: &mut flatbuffers::FlatBufferBuilder) -> flatbuffers::WIPOffset<Foo> {
/// #         flatbuffers::WIPOffset::new(0)
/// #     }
/// # }
/// #
/// let mut b = oak_idl::MessageBuilder::<Foo>::default();
/// let v = b.create_vector::<u8>(&[14, 12]);
/// let foo = Foo::create(&mut b);
/// let m = b.finish(foo);
/// ```
pub struct MessageBuilder<'a, T> {
    buf: flatbuffers::FlatBufferBuilder<'a>,
    _phantom: PhantomData<T>,
}

impl<'a, T: flatbuffers::Verifiable + flatbuffers::Follow<'a>> Default for MessageBuilder<'a, T> {
    fn default() -> Self {
        Self {
            buf: flatbuffers::FlatBufferBuilder::default(),
            _phantom: PhantomData,
        }
    }
}

impl<'a, T: flatbuffers::Verifiable + flatbuffers::Follow<'a>> MessageBuilder<'a, T> {
    pub fn finish(
        self,
        offset: flatbuffers::WIPOffset<T>,
    ) -> Result<Message<T>, flatbuffers::InvalidFlatbuffer> {
        let mut s = self;
        s.buf.finish(offset, None);
        Message::from_vec(s.buf.finished_data().to_vec())
    }
}

/// Delegate most methods to the underlying [`MessageBuilder`].
impl<'a, T> Deref for MessageBuilder<'a, T> {
    type Target = flatbuffers::FlatBufferBuilder<'a>;

    fn deref(&self) -> &Self::Target {
        &self.buf
    }
}

/// Delegate most methods to the underlying [`MessageBuilder`].
impl<'a, T> DerefMut for MessageBuilder<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.buf
    }
}

/// An owned flatbuffer message, which owns the underlying buffer.
pub struct Message<T> {
    buf: Vec<u8>,
    _phantom: PhantomData<T>,
}

impl<T: flatbuffers::Verifiable> Message<T> {
    pub fn from_vec(buf: Vec<u8>) -> Result<Self, flatbuffers::InvalidFlatbuffer> {
        use flatbuffers::Verifiable;
        let opts = flatbuffers::VerifierOptions::default();
        let mut v = flatbuffers::Verifier::new(&opts, &buf);
        <flatbuffers::ForwardsUOffset<T>>::run_verifier(&mut v, 0)?;
        Ok(Self {
            buf,
            _phantom: PhantomData,
        })
    }
}

impl<T> Message<T> {
    /// Returns a reference to the underlying owned buffer.
    pub fn buf(&self) -> &[u8] {
        &self.buf
    }
}

impl<'a, T: flatbuffers::Follow<'a> + flatbuffers::Verifiable> Message<T> {
    /// Returns a reference to the flatbuffer object, pointing within the underlying owned buffer.
    pub fn get(&'a self) -> T::Inner {
        flatbuffers::root::<T>(&self.buf).unwrap()
    }
}

/// A low-level message-oriented transport over channels. This is meant to emulate the low-level
/// Wasm ABI in Oak, and will eventually be replaced by that.
fn invoke(_channel_handle: u32, _request: &[u8]) -> Result<Vec<u8>, TransportError> {
    unimplemented!()
}
