//
// Copyright 2020 The Project Oak Authors
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

//! gRPC related types for asynchronous processing.

use crate::{io::ReceiverAsync, ChannelReadStream};
use core::{
    pin::Pin,
    task::{Context, Poll},
};
use futures::stream::{Peek, Peekable, Stream, StreamExt};
use log::error;
use oak::{
    grpc::{ChannelResponseWriter, Code, GrpcRequest, Invocation, WriteMode},
    io::{Decodable, Message},
    OakError, OakStatus,
};

/// Writes exactly one message on a gRPC response channel, setting an `UNKNOWN` error if unused.
///
/// This type is used for gRPC methods where the return type is non-streaming. Instances must be
/// consumed using [`send`](#method.send). In exceptional circumstances the
/// [`into_inner`](#method.into_inner) method may be used to access the underlying
/// `ChannelResponseWriter`.
///
/// If neither [`send`](#method.send) nor [`into_inner`](#method.into_inner) is called, an `UNKNOWN`
/// error will be written as the response upon [`Drop`](#impl-Drop).
#[must_use = "exactly one message should be sent. Use into_inner for advanced use cases"]
pub struct OneshotWriter<T> {
    writer: Option<ChannelResponseWriter>,
    _msg: core::marker::PhantomData<T>,
}

impl<T: ::prost::Message> OneshotWriter<T> {
    // Only for use by the Oak Service Generator.
    #[doc(hidden)]
    pub fn new(writer: ChannelResponseWriter) -> OneshotWriter<T> {
        OneshotWriter {
            writer: Some(writer),
            _msg: core::marker::PhantomData,
        }
    }

    /// Send the response, automatically closing the channel.
    pub fn send(mut self, msg: &T) -> Result<(), OakError> {
        self.writer.take().unwrap().write(msg, WriteMode::Close)?;
        Ok(())
    }

    /// Closes the channel with the given error code and message.
    pub fn close_error<S: AsRef<str>>(mut self, code: Code, msg: S) -> Result<(), OakError> {
        self.writer
            .take()
            .unwrap()
            .close(Err(oak::grpc::build_status(code, msg.as_ref())))?;
        Ok(())
    }

    /// Consumes this writer, returning a `ChannelResponseWriter` in its place.
    pub fn into_inner(mut self) -> ChannelResponseWriter {
        self.writer.take().unwrap()
    }
}

impl<T> Drop for OneshotWriter<T> {
    /// Close the channel with an `Unknown` status if no message was sent.
    fn drop(&mut self) {
        if let Some(writer) = self.writer.take() {
            error!("drop() called on OneshotWriter");
            if let Err(e) = writer.close(Err(oak::grpc::build_status(Code::Unknown, ""))) {
                error!("Failed to close OneshotWriter in Drop: {}", e);
            }
        }
    }
}

/// Writes multiple messages to a gRPC response channel, automatically closing the channel on
/// `drop()`.
///
/// This type is used for gRPC methods where the return type is streaming.
///
///
/// In exceptional circumstances the [`into_inner`](#method.into_inner) method may be used to access
/// the underlying `ChannelResponseWriter`.
pub struct MultiWriter<T> {
    writer: Option<ChannelResponseWriter>,
    _msg: core::marker::PhantomData<T>,
}

impl<T: ::prost::Message> MultiWriter<T> {
    // Only for use by the Oak Service Generator.
    #[doc(hidden)]
    pub fn new(writer: ChannelResponseWriter) -> MultiWriter<T> {
        MultiWriter {
            writer: Some(writer),
            _msg: core::marker::PhantomData,
        }
    }

    /// Send a response to the channel.
    pub fn send(&self, msg: &T) -> Result<(), OakError> {
        self.writer
            .as_ref()
            .unwrap()
            .write(msg, WriteMode::KeepOpen)
    }

    /// Closes the channel with the given error code and message.
    ///
    /// To return an `Ok` status, prefer simply dropping the writer or explicitly calling `drop()`.
    pub fn close_error<S: AsRef<str>>(mut self, code: Code, msg: S) -> Result<(), OakError> {
        self.writer
            .take()
            .unwrap()
            .close(Err(oak::grpc::build_status(code, msg.as_ref())))?;
        Ok(())
    }

    /// Consumes this writer, returning a `ChannelResponseWriter` in its place.
    pub fn into_inner(mut self) -> ChannelResponseWriter {
        self.writer.take().unwrap()
    }
}

impl<T> Drop for MultiWriter<T> {
    /// Close the channel with an `Ok` status.
    fn drop(&mut self) {
        if let Some(writer) = self.writer.take() {
            if let Err(e) = writer.close(Ok(())) {
                error!("Failed to close MultiWriter in Drop: {}", e);
            };
        }
    }
}

/// A streaming gRPC client request.
///
/// `T` represents the message type sent in the requests.
pub struct GrpcRequestStream<T: Decodable> {
    inner: Peekable<ChannelReadStream<GrpcRequest>>,
    is_drained: bool,
    _msg: core::marker::PhantomData<T>,
}

// Unpin is needed to be able to peek at the first request before passing it
// on to the handler.
impl<T: Decodable> Unpin for GrpcRequestStream<T> {}

impl GrpcRequestStream<()> {
    fn new(inner: ChannelReadStream<GrpcRequest>) -> GrpcRequestStream<()> {
        GrpcRequestStream {
            inner: inner.peekable(),
            is_drained: false,
            _msg: core::marker::PhantomData,
        }
    }

    // Casts this stream into the given message type.
    // This should only be used by the Oak service generator. Not a stable API.
    #[doc(hidden)]
    pub fn into_type<T: Decodable>(self) -> GrpcRequestStream<T> {
        GrpcRequestStream {
            inner: self.inner,
            is_drained: self.is_drained,
            _msg: core::marker::PhantomData,
        }
    }
}

// This should only be used by the Oak service generator. Not a stable API.
#[doc(hidden)]
impl<T: Decodable> GrpcRequestStream<T> {
    pub fn peek(self: Pin<&mut Self>) -> Peek<'_, ChannelReadStream<GrpcRequest>> {
        Peekable::peek(Pin::new(&mut Pin::into_inner(self).inner))
    }

    pub async fn first(mut self) -> Result<T, OakError> {
        // Unwrapping is safe here, as the gRPC stream must have at least one incoming request
        self.next().await.unwrap()
    }
}

impl<T: Decodable> Stream for GrpcRequestStream<T> {
    type Item = Result<T, OakError>;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        if self.is_drained {
            return Poll::Ready(None);
        }
        let self_ = Pin::into_inner(self);
        let inner = Pin::new(&mut self_.inner);
        Peekable::poll_next(inner, cx).map(|ready| {
            ready.map(|some| {
                some.and_then(|request| {
                    self_.is_drained = request.last;
                    let message = Message {
                        bytes: request.req_msg,
                        handles: Vec::new(),
                    };
                    T::decode(&message)
                })
            })
        })
    }
}

// A gRPC invocation decomposed into the method, request stream and response writer.
// This should only be used by the Oak service generator. Not a stable API.
#[doc(hidden)]
pub struct DecomposedInvocation {
    pub method: String,
    pub requests: GrpcRequestStream<()>,
    pub response_writer: ChannelResponseWriter,
}

impl DecomposedInvocation {
    pub async fn from(invocation: Invocation) -> Result<DecomposedInvocation, OakError> {
        let receiver = invocation.receiver.ok_or_else(|| {
            error!("Invocation did not have a receiver");
            OakError::OakStatus(OakStatus::ErrInvalidArgs)
        })?;
        let mut requests = GrpcRequestStream::new(receiver.receive_stream());
        let requests_pinned = core::pin::Pin::new(&mut requests);
        let sender = invocation.sender.ok_or_else(|| {
            error!("Invocation did not have a sender");
            OakError::OakStatus(OakStatus::ErrInvalidArgs)
        })?;
        let response_writer = ChannelResponseWriter::new(sender);

        let method = match requests_pinned
            .peek()
            .await
            .ok_or_else(|| {
                error!("No request arrived for invocation");
                OakError::OakStatus(OakStatus::ErrBadHandle)
            })?
            .as_ref()
        {
            Ok(req) => req.method_name.clone(),
            Err(_) => {
                // Pull the error out of the stream instead of just peeking so we can own it.
                let owned_err = requests.next().await;
                match owned_err {
                    Some(Err(e)) => return Err(e),
                    // We have already established that the next item on the stream exists and is an
                    // error by peeking at it
                    _ => unreachable!(),
                }
            }
        };
        Ok(DecomposedInvocation {
            method,
            requests,
            response_writer,
        })
    }
}
