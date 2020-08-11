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

use crate::{io::Encodable, OakError, OakStatus, WriteHandle};
use prost::{
    bytes::{Buf, BufMut},
    encoding::{DecodeContext, WireType},
};

/// Wrapper for a handle to the send half of a channel, allowing to send data that can be encoded as
/// bytes + handles via the `Encodable` trait.
///
/// For use when the underlying [`Handle`] is known to be for a send half.
///
/// [`Handle`]: crate::Handle
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Sender<T: Encodable> {
    pub handle: WriteHandle,
    phantom: std::marker::PhantomData<T>,
}

/// Trait for context-dependent functionality on a `Sender`.
pub trait SenderExt<T> {
    /// Close the underlying channel used by the sender.
    fn send(&self, t: &T) -> Result<(), OakError>;

    /// Attempt to send a value on the sender.
    fn close(&self) -> Result<(), OakStatus>;
}

impl<T: Encodable> SenderExt<T> for Sender<T> {
    /// Close the underlying channel used by the sender.
    fn close(&self) -> Result<(), OakStatus> {
        crate::channel_close(self.handle.handle)
    }

    /// Attempt to send a value on the sender.
    fn send(&self, t: &T) -> Result<(), OakError> {
        let message = t.encode()?;
        crate::channel_write(self.handle, &message.bytes, &message.handles)?;
        Ok(())
    }
}

impl<T: Encodable> Sender<T> {
    pub fn new(handle: WriteHandle) -> Self {
        Sender {
            handle,
            phantom: std::marker::PhantomData,
        }
    }
}

impl<T: Encodable> crate::handle::HandleVisit for Sender<T> {
    fn visit<F: FnMut(&mut crate::Handle)>(&mut self, mut visitor: F) -> F {
        visitor(&mut self.handle.handle);
        visitor
    }
}

impl<T: Encodable> Sender<T> {
    pub fn as_proto_handle(&self) -> crate::handle::Sender {
        crate::handle::Sender {
            id: self.handle.handle,
        }
    }
}

// Lean on the auto-generated impl of oak::handle::Sender.
impl<T: Send + Sync + core::fmt::Debug + Encodable> prost::Message for Sender<T> {
    fn encoded_len(&self) -> usize {
        self.as_proto_handle().encoded_len()
    }

    fn clear(&mut self) {
        self.handle.handle = crate::handle::invalid();
    }

    fn encode_raw<B: BufMut>(&self, buf: &mut B) {
        self.as_proto_handle().encode_raw(buf);
    }

    fn merge_field<B: Buf>(
        &mut self,
        tag: u32,
        wire_type: WireType,
        buf: &mut B,
        ctx: DecodeContext,
    ) -> Result<(), prost::DecodeError> {
        let mut proto = self.as_proto_handle();
        proto.merge_field(tag, wire_type, buf, ctx)?;
        self.handle.handle = proto.id;
        Ok(())
    }
}

impl<T: Encodable> Default for Sender<T> {
    fn default() -> Sender<T> {
        Sender::new(WriteHandle {
            handle: crate::handle::invalid(),
        })
    }
}
