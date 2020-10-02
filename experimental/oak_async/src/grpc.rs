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

use log::error;
use oak::{
    grpc::{ChannelResponseWriter, Code, WriteMode},
    OakError,
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
