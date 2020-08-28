//! Asynchronous I/O

use crate::executor::with_executor;
use core::{
    future::Future,
    marker::PhantomData,
    pin::Pin,
    task::{Context, Poll},
};
use oak::{
    io::{Decodable, Message},
    OakError, OakStatus, ReadHandle,
};

pub struct ChannelRead<T: Decodable> {
    reader_id: usize,
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
        with_executor(|e| e.remove_waiting_reader(self.reader_id))
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

pub trait ReceiverAsync {
    type Message: Decodable;
    fn receive_async(&self) -> ChannelRead<Self::Message>;
}

impl<T: Decodable + Send> ReceiverAsync for oak::io::Receiver<T> {
    type Message = T;

    fn receive_async(&self) -> ChannelRead<Self::Message> {
        ChannelRead::new(self.handle)
    }
}
