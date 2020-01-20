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

use crate::io::Decodable;
use crate::{OakError, OakStatus, ReadHandle};
use serde::{Deserialize, Serialize};

/// Wrapper for a handle to the read half of a channel, allowing to receive data that can be decoded
/// as bytes + handles via the `Decodable` trait.
///
/// For use when the underlying [`Handle`] is known to be for a receive half.
#[derive(Debug, Copy, Clone, PartialEq, Serialize, Deserialize)]
pub struct Receiver {
    pub handle: ReadHandle,
}

impl Receiver {
    pub fn new(handle: ReadHandle) -> Self {
        Receiver { handle }
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
    pub fn receive<T>(&self) -> Result<T, OakError>
    where
        T: Decodable,
    {
        self.wait()?;
        self.try_receive()
    }

    /// Attempt to read a value from this receiver, without blocking.
    ///
    /// See https://doc.rust-lang.org/std/sync/mpsc/struct.Receiver.html#method.try_recv
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub fn try_receive<T>(&self) -> Result<T, OakError>
    where
        T: Decodable,
    {
        let mut bytes = Vec::with_capacity(1024);
        let mut handles = Vec::with_capacity(16);
        crate::channel_read(self.handle, &mut bytes, &mut handles)?;
        // `bytes` and `handles` are moved into `Message`, so there is no extra copy happening here.
        let message = crate::io::Message { bytes, handles };
        T::decode(&message)
    }

    /// Wait for a value to be available from this receiver.
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub fn wait(&self) -> Result<(), OakStatus> {
        // TODO(#500): Consider creating the handle notification space once and for all in `new`.
        let read_handles = vec![self.handle];
        let mut space = crate::new_handle_space(&read_handles);
        crate::prep_handle_space(&mut space);
        let status =
            unsafe { oak_abi::wait_on_channels(space.as_mut_ptr(), read_handles.len() as u32) };
        crate::result_from_status(status as i32, ())
    }
}
