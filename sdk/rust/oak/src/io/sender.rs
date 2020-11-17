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
    io::{Encodable, Sender},
    Label, OakError, OakStatus,
};

/// Trait for context-dependent functionality on a `Sender`.
pub trait SenderExt<T> {
    /// Closes the underlying channel used by the sender.
    fn close(&self) -> Result<(), OakStatus>;

    /// Attempts to send a value on the sender.
    fn send(&self, t: &T) -> Result<(), OakError>;

    /// Attempts to send a value on the sender using the current node's label-downgrading privilege.
    fn send_with_privilege(&self, t: &T) -> Result<(), OakError>;

    /// Retrieves the label associated with the underlying channel.
    fn label(&self) -> Result<Label, OakError>;
}

impl<T: Encodable> SenderExt<T> for Sender<T> {
    fn close(&self) -> Result<(), OakStatus> {
        crate::channel_close(self.handle.handle)
    }

    fn send(&self, t: &T) -> Result<(), OakError> {
        let message = t.encode()?;
        crate::channel_write(self.handle, &message.bytes, &message.handles)?;
        Ok(())
    }

    fn send_with_privilege(&self, t: &T) -> Result<(), OakError> {
        let message = t.encode()?;
        crate::channel_write_with_privilege(self.handle, &message.bytes, &message.handles)?;
        Ok(())
    }

    fn label(&self) -> Result<Label, OakError> {
        let label = crate::channel_label_read(self.handle.handle)?;
        Ok(label)
    }
}
