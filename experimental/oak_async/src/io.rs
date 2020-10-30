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

//! Asynchronous I/O

use crate::executor::{with_executor, ReaderId};
use core::{
    future::Future,
    marker::PhantomData,
    pin::Pin,
    task::{Context, Poll},
};
use futures::stream::Stream;
use log::{debug, error, info};
use oak::{
    io::{Decodable, Message, Receiver},
    OakError, OakStatus, ReadHandle,
};

/// `Future` representing an asynchronous read from a channel.
pub struct ChannelRead<T: Decodable> {
    reader_id: ReaderId,
    handle: ReadHandle,
    _message_type: PhantomData<T>,
}

impl<T: Decodable> ChannelRead<T> {
    fn new(handle: ReadHandle) -> ChannelRead<T> {
        ChannelRead {
            reader_id: with_executor(|e| e.new_id()),
            handle,
            _message_type: PhantomData,
        }
    }
}

impl<T: Decodable> Future for ChannelRead<T> {
    type Output = Result<T, OakError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
        // Check for ready status on the channel before scheduling a wakeup from the executor, in
        // case we don't need to wait.
        if let Some(data) = channel_read_message(self.handle) {
            Poll::Ready(data)
        } else {
            with_executor(|e| e.add_waiting_reader(self.reader_id, self.handle, cx.waker()));
            Poll::Pending
        }
    }
}

impl<T: Decodable> Drop for ChannelRead<T> {
    fn drop(&mut self) {
        with_executor(|e| {
            debug!("Dropping reader {}", self.reader_id);
            // Remove the reader from the waiting set, or the executor will keep waiting for
            // data on this channel (which might never come).
            e.remove_waiting_reader(self.reader_id)
        })
    }
}

/// `Stream` representing a sequence of asynchronous reads from a channel.
pub struct ChannelReadStream<T: Decodable>(
    // Note: `Stream` could be implemented directly on the `ChannelRead` type, but unfortunately
    // the `Future` and `Stream` extension traits have some methods that overlap, such as
    // `map`. This would make it impossible for the compiler to figure out what a call like
    // `my_channel_read.map(..)`  should do, so instead the stream is wrapped in its own type to
    // avoid any confusion.
    ChannelRead<T>,
);

impl<T: Decodable> Stream for ChannelReadStream<T> {
    type Item = Result<T, OakError>;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
        // This is trivially safe, as the inner contents of the struct are never moved or even
        // mutated.
        let inner = unsafe { self.map_unchecked_mut(|s| &mut s.0) };
        match inner.poll(cx) {
            // ErrChannelClosed indicates the end of the stream
            Poll::Ready(Err(OakError::OakStatus(OakStatus::ErrChannelClosed))) => Poll::Ready(None),
            Poll::Ready(data) => Poll::Ready(Some(data)),
            Poll::Pending => Poll::Pending,
        }
    }
}

fn channel_read_message<T: Decodable>(handle: ReadHandle) -> Option<Result<T, OakError>> {
    let mut message = Message {
        bytes: Vec::new(),
        handles: Vec::new(),
    };
    match oak::channel_read(handle, &mut message.bytes, &mut message.handles) {
        Ok(()) => Some(T::decode(&message)),
        Err(OakStatus::ErrChannelEmpty) => None,
        Err(e) => Some(Err(OakError::from(e))),
    }
}

/// Extension trait to allow asynchronous reads from a `Receiver`.
pub trait ReceiverAsync {
    type Message: Decodable;

    /// Asynchronously receive a message.
    ///
    /// The returned `Future` resolves to either a message or an `OakError`.
    fn receive_async(&self) -> ChannelRead<Self::Message>;

    /// Asynchronously receive multiple messages.
    ///
    /// Each item received from this `Stream` resolves to either a message or an `OakError`
    fn receive_stream(&self) -> ChannelReadStream<Self::Message> {
        ChannelReadStream(self.receive_async())
    }
}

impl<T: Decodable + Send> ReceiverAsync for Receiver<T> {
    type Message = T;

    fn receive_async(&self) -> ChannelRead<Self::Message> {
        ChannelRead::new(self.handle)
    }
}

/// Process the stream of messages coming in on `receiver` using the provided handler.
///
/// If the runtime signals that the node is being terminated while waiting for new commands, the
/// loop will terminate and this function will return without completing the `handler` future.
///
/// `panic!`s if any other error occurs while reading commands.
pub fn run_command_loop<T, F, R>(receiver: Receiver<T>, handler: F)
where
    T: Decodable + Send,
    F: FnOnce(ChannelReadStream<T>) -> R,
    R: Future<Output = ()> + 'static,
{
    match crate::block_on(handler(receiver.receive_stream())) {
        Ok(()) => {}
        Err(OakStatus::ErrTerminated) => {
            info!("Received termination status, terminating command loop");
        }
        Err(e) => error!("Command loop received non-termination error: {:?}", e),
    }
}
