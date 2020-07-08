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

use crate::{io::Decodable, ChannelReadStatus, OakError, OakStatus, ReadHandle};
use log::error;
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

    /// Close the underlying channel used by this receiver.
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub fn close(&self) -> Result<(), OakStatus> {
        crate::channel_close(self.handle.handle)
    }

    /// Attempt to wait for a value on this receiver, blocking if necessary.
    ///
    /// See https://doc.rust-lang.org/std/sync/mpsc/struct.Receiver.html#method.recv
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub fn receive(&self) -> Result<T, OakError> {
        self.wait()?;
        self.try_receive()
    }

    /// Attempt to read a value from this receiver, without blocking.
    ///
    /// See https://doc.rust-lang.org/std/sync/mpsc/struct.Receiver.html#method.try_recv
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub fn try_receive(&self) -> Result<T, OakError> {
        let mut bytes = Vec::with_capacity(1024);
        let mut handles = Vec::with_capacity(16);
        crate::channel_read(self.handle, &mut bytes, &mut handles)?;
        // `bytes` and `handles` are moved into `Message`, so there is no extra copy happening here.
        let message = crate::io::Message { bytes, handles };
        T::decode(&message)
    }

    /// Wait for a value to be available from this receiver.
    ///
    /// Returns [`ChannelReadStatus`] of the wrapped handle, or `Err(OakStatus::ErrTerminated)` if
    /// the Oak Runtime is terminating.
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub fn wait(&self) -> Result<ChannelReadStatus, OakStatus> {
        // TODO(#500): Consider creating the handle notification space once and for all in `new`.
        let read_handles = vec![self.handle];
        let mut space = crate::new_handle_space(&read_handles);
        crate::prep_handle_space(&mut space);
        let status =
            unsafe { oak_abi::wait_on_channels(space.as_mut_ptr(), read_handles.len() as u32) };

        match crate::result_from_status(status as i32, ()) {
            Ok(()) => space
                .get(oak_abi::SPACE_BYTES_PER_HANDLE - 1)
                .cloned()
                .map(i32::from)
                .and_then(ChannelReadStatus::from_i32)
                .ok_or_else(|| {
                    error!(
                        "Should never get here. `wait_on_channels` always yields a valid `ChannelReadStatus` if the returned status is not Err(OakStatus::ErrTerminated)."
                    );
                    OakStatus::ErrInternal
                }),
            Err(OakStatus::ErrTerminated) => Err(OakStatus::ErrTerminated),
            Err(OakStatus::ErrInvalidArgs) => {
                error!("Should never get here. `ErrInvalidArgs` here indicates that `space` is corrupted.");
                Err(OakStatus::ErrInternal)
            }
            Err(status) => {
                error!("Should never get here. `wait_on_channels` should never return {:?}.", status);
                Err(OakStatus::ErrInternal)
            }
        }
    }
}

impl<T: Decodable> crate::handle::HandleVisit for Receiver<T> {
    fn visit<F: FnMut(&mut crate::handle::Handle)>(&mut self, mut visitor: F) -> F {
        visitor(&mut self.handle.handle.id);
        visitor
    }
}

impl<T: Decodable> Receiver<T> {
    pub fn as_proto_handle(&self) -> crate::handle::Receiver {
        crate::handle::Receiver {
            id: self.handle.handle.id,
        }
    }
}

// Lean on the auto-generated impl of oak::handle::Receiver.
impl<T: Send + Sync + core::fmt::Debug + Decodable> prost::Message for Receiver<T> {
    fn encoded_len(&self) -> usize {
        self.as_proto_handle().encoded_len()
    }

    fn clear(&mut self) {
        self.handle.handle.id = 0;
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
        self.handle.handle.id = proto.id;
        Ok(())
    }
}

impl<T: Decodable> Default for Receiver<T> {
    fn default() -> Receiver<T> {
        Receiver::new(ReadHandle {
            handle: crate::Handle::invalid(),
        })
    }
}
