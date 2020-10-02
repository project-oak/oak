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
use log::debug;
use oak::{
    io::{Decodable, Message},
    OakError, OakStatus, ReadHandle,
};

/// `Future` representing an asynchronous read from a channel.
pub struct ChannelRead<T: Decodable> {
    reader_id: ReaderId,
    handle: ReadHandle,
    _message_type: PhantomData<T>,
}

impl<T: Decodable> ChannelRead<T> {
    pub(crate) fn new(handle: ReadHandle) -> ChannelRead<T> {
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
}

impl<T: Decodable + Send> ReceiverAsync for oak::io::Receiver<T> {
    type Message = T;

    fn receive_async(&self) -> ChannelRead<Self::Message> {
        ChannelRead::new(self.handle)
    }
}
