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

use crate::OakStatus;
use oak_abi::{label::Label, proto::oak::application::NodeConfiguration};
pub use oak_io::{Decodable, Encodable, Receiver, Sender};

/// Convenience struct for building Nodes.
pub struct NodeBuilder {
    config: NodeConfiguration,
    label: Option<Label>,
}

// TODO(#1584): Send init messages as a part of building process.
impl NodeBuilder {
    pub fn new(config: &NodeConfiguration) -> Self {
        Self {
            config: config.clone(),
            label: None,
        }
    }

    /// Set `label` for both newly created Node and a corresponding initial channel to this Node.
    pub fn label<'a>(&'a mut self, label: &Label) -> &'a mut Self {
        self.label = Some(label.clone());
        self
    }

    /// Build Node using provided [`NodeBuilder::config`] and [`NodeBuilder::label`].
    /// If [`NodeBuilder::label`] is `None` - uses [`Label::public_untrusted`].
    /// Returns [`Sender`] for the initial channel to the newly created Node.
    pub fn build<T: Encodable + Decodable>(&self) -> Result<Sender<T>, OakStatus> {
        let public_label = Label::public_untrusted();
        let label = self.label.as_ref().unwrap_or(&public_label);
        let (sender, receiver) = crate::io::channel_create_with_label::<T>(&label)?;
        crate::node_create_with_label(&self.config, &label, receiver.handle)?;
        crate::channel_close(receiver.handle.handle)?;
        Ok(sender)
    }
}
