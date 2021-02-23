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

use crate::{
    io::{Decodable, Receiver},
    ChannelReadStatus, Label, OakError, OakStatus,
};
use log::{debug, error, info, trace, warn};

/// SDK-specific functionality provided by a receiver.
pub trait ReceiverExt<T: Decodable> {
    /// Closes the underlying channel used by the receiver.
    fn close(&self) -> Result<(), OakStatus>;

    /// Attempts to wait for a value on the receiver, blocking if necessary.
    fn receive(&self) -> Result<T, OakError>;

    /// The same as [`receive`](#method.receive), but also applies the current Node's
    /// downgrade privilege when checking IFC restrictions.
    fn receive_with_downgrade(&self) -> Result<T, OakError>;

    /// Attempts to read a value from the receiver, without blocking.
    fn try_receive(&self) -> Result<T, OakError>;

    /// The same as [`try_receive`](#method.try_receive), but also applies the current Node's
    /// downgrade privilege when checking IFC restrictions.
    fn try_receive_with_downgrade(&self) -> Result<T, OakError>;

    /// Retrieves the label associated with the underlying channel.
    fn label(&self) -> Result<Label, OakError>;

    /// Waits for a value to be available from the receiver.
    ///
    /// Returns [`ChannelReadStatus`] of the wrapped handle, or `Err(OakStatus::ErrTerminated)` if
    /// the Oak Runtime is terminating.
    fn wait(&self) -> Result<ChannelReadStatus, OakStatus>;

    /// The same as [`wait`](#method.wait), but also applies the current Node's downgrade privilege
    /// when checking IFC restrictions.
    fn wait_with_downgrade(&self) -> Result<ChannelReadStatus, OakStatus>;

    /// Consumes the receiver and returns an iterator that will block waiting for messages. It will
    /// return None when the node terminates, or a non-transient error occurs when reading from the
    /// channel. Transient errors will be silently ignored by this iterator, including cases in
    /// which the incoming message cannot be decoded correctly.
    ///
    /// Also see [`std::sync::mpsc::Receiver::iter`].
    fn iter(self) -> ReceiverIterator<T>;
}

/// Blocking iterator over incoming messages, created via [`ReceiverExt::iter`].
pub struct ReceiverIterator<T: Decodable> {
    inner: Receiver<T>,
}

impl<T: Decodable> Iterator for ReceiverIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let receiver = &self.inner;
        loop {
            match receiver.wait() {
                Err(status) => {
                    use crate::OakStatus::*;
                    match status {
                        ErrTerminated => {
                            info!(
                            "{:?}: received node termination status: {:?}; terminating iterator",
                            receiver, status
                        );
                            return None;
                        }
                        _ => {
                            error!(
                            "{:?}: received status: {:?}; but `Receiver::wait` should never return an error other than `ErrTerminated`",
                            receiver, status
                        );
                            return None;
                        }
                    }
                }
                Ok(status) => match status {
                    ChannelReadStatus::ReadReady => trace!("{:?}: wait over", receiver),
                    ChannelReadStatus::Orphaned
                    | ChannelReadStatus::PermissionDenied
                    | ChannelReadStatus::InvalidChannel => {
                        warn!(
                        "{:?}: received invalid channel read status: {:?}; terminating iterator",
                        receiver, status
                    );
                        return None;
                    }
                    ChannelReadStatus::NotReady => {
                        error!(
                        "{:?}: received `ChannelReadStatus::NotReady`, which should never be returned from `Receiver::wait`.",
                        receiver);
                        return None;
                    }
                },
            }
            match receiver.try_receive() {
                Ok(m) => {
                    debug!("{:?}: received message", receiver);
                    return Some(m);
                }
                Err(err) => {
                    // Log error and continue with the next iteration.
                    // We do this because the error may have been caused by an invalid or malformed
                    // message, and we don't want to terminate the iterator early if that's the
                    // case.
                    error!("{:?}: error receiving message: {}", receiver, err);
                }
            }
        }
    }
}

impl<T: Decodable> ReceiverExt<T> for Receiver<T> {
    fn close(&self) -> Result<(), OakStatus> {
        crate::channel_close(self.handle.handle)
    }

    fn receive(&self) -> Result<T, OakError> {
        let status = self.wait()?;
        match status {
            ChannelReadStatus::ReadReady => self.try_receive(),
            ChannelReadStatus::PermissionDenied => {
                warn!(
                    "{:?}: received permission denied read status: {:?}",
                    &self, status
                );
                Err(OakError::OakStatus(OakStatus::ErrPermissionDenied))
            }
            ChannelReadStatus::Orphaned => {
                warn!("{:?}: received orphaned read status: {:?}", &self, status);
                Err(OakError::OakStatus(OakStatus::ErrChannelClosed))
            }
            ChannelReadStatus::InvalidChannel => {
                warn!(
                    "{:?}: received invalid channel read status: {:?}",
                    &self, status
                );
                Err(OakError::OakStatus(OakStatus::ErrBadHandle))
            }
            ChannelReadStatus::NotReady => {
                error!(
                    "{:?}: received `ChannelReadStatus::NotReady`, which should never be returned from `Receiver::wait`",
                    &self
                );
                Err(OakError::OakStatus(OakStatus::ErrInternal))
            }
        }
    }

    fn receive_with_downgrade(&self) -> Result<T, OakError> {
        self.wait_with_downgrade()?;
        self.try_receive_with_downgrade()
    }

    fn try_receive(&self) -> Result<T, OakError> {
        let mut bytes = Vec::with_capacity(1024);
        let mut handles = Vec::with_capacity(16);
        crate::channel_read(&self.handle, &mut bytes, &mut handles)?;
        // `bytes` and `handles` are moved into `Message`, so there is no extra copy happening here.
        let message = crate::io::Message { bytes, handles };
        T::decode(&message)
    }

    fn try_receive_with_downgrade(&self) -> Result<T, OakError> {
        let mut bytes = Vec::with_capacity(1024);
        let mut handles = Vec::with_capacity(16);
        crate::channel_read_with_downgrade(&self.handle, &mut bytes, &mut handles)?;
        // `bytes` and `handles` are moved into `Message`, so there is no extra copy happening here.
        let message = crate::io::Message { bytes, handles };
        T::decode(&message)
    }

    fn label(&self) -> Result<Label, OakError> {
        let label = crate::channel_label_read(self.handle.handle)?;
        Ok(label)
    }

    fn wait(&self) -> Result<ChannelReadStatus, OakStatus> {
        // TODO(#500): Consider creating the handle notification space once and for all in `new`.
        let read_handles = vec![&self.handle];
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

    fn wait_with_downgrade(&self) -> Result<ChannelReadStatus, OakStatus> {
        // TODO(#500): Consider creating the handle notification space once and for all in `new`.
        let read_handles = vec![&self.handle];
        let mut space = crate::new_handle_space(&read_handles);
        crate::prep_handle_space(&mut space);
        let status = unsafe {
            oak_abi::wait_on_channels_with_downgrade(space.as_mut_ptr(), read_handles.len() as u32)
        };

        match crate::result_from_status(status as i32, ()) {
            Ok(()) => space
                .get(oak_abi::SPACE_BYTES_PER_HANDLE - 1)
                .cloned()
                .map(i32::from)
                .and_then(ChannelReadStatus::from_i32)
                .ok_or_else(|| {
                    error!(
                        "Should never get here. `wait_on_channels_with_downgrade` always yields a valid `ChannelReadStatus` if the returned status is not Err(OakStatus::ErrTerminated)."
                    );
                    OakStatus::ErrInternal
                }),
            Err(OakStatus::ErrTerminated) => Err(OakStatus::ErrTerminated),
            Err(OakStatus::ErrInvalidArgs) => {
                error!("Should never get here. `ErrInvalidArgs` here indicates that `space` is corrupted.");
                Err(OakStatus::ErrInternal)
            }
            Err(status) => {
                error!("Should never get here. `wait_on_channels_with_downgrade` should never return {:?}.", status);
                Err(OakStatus::ErrInternal)
            }
        }
    }

    fn iter(self) -> ReceiverIterator<T> {
        ReceiverIterator { inner: self }
    }
}
