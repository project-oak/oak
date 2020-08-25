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

use crate::{Decodable, ReadHandle};
use prost::{
    bytes::{Buf, BufMut},
    encoding::{DecodeContext, WireType},
};

/// Wrapper for a handle to the read half of a channel, allowing to receive data that can be decoded
/// as bytes + handles via the `Decodable` trait.
///
/// For use when the underlying [`Handle`] is known to be for a receive half.
///
/// [`Handle`]: crate::Handle
#[derive(Copy, Clone, PartialEq)]
pub struct Receiver<T: Decodable> {
    pub handle: ReadHandle,
    phantom: std::marker::PhantomData<T>,
}

/// Manual implementation of [`std::fmt::Debug`] for any `T`.
///
/// The automatically derived implementation would only cover types `T` that are themselves
/// `Display`, but we do not care about that bound, since there is never an actual element of type
/// `T` to display.
impl<T: Decodable> std::fmt::Debug for Receiver<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "Receiver({:?})", self.handle)
    }
}

impl<T: Decodable> Receiver<T> {
    pub fn new(handle: ReadHandle) -> Self {
        Receiver {
            handle,
            phantom: std::marker::PhantomData,
        }
    }
}

impl<T: Decodable> crate::handle::HandleVisit for Receiver<T> {
    fn visit<F: FnMut(&mut crate::Handle)>(&mut self, mut visitor: F) -> F {
        visitor(&mut self.handle.handle);
        visitor
    }
}

impl<T: Decodable> Receiver<T> {
    pub fn as_proto_handle(&self) -> crate::handle::Receiver {
        crate::handle::Receiver {
            id: self.handle.handle,
        }
    }
}

// Lean on the auto-generated impl of oak::handle::Receiver.
impl<T: Send + Sync + core::fmt::Debug + Decodable> prost::Message for Receiver<T> {
    fn encoded_len(&self) -> usize {
        self.as_proto_handle().encoded_len()
    }

    fn clear(&mut self) {
        self.handle.handle = oak_abi::INVALID_HANDLE;
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

impl<T: Decodable> Default for Receiver<T> {
    fn default() -> Receiver<T> {
        Receiver::new(ReadHandle {
            handle: oak_abi::INVALID_HANDLE,
        })
    }
}
