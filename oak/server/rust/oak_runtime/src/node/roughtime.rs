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

use crate::runtime::RuntimeProxy;
use log::{info, warn};
use tokio::sync::oneshot;

/// Roughtime client pseudo-Node.
pub struct RoughtimeClientNode {
    node_name: String,
}

impl RoughtimeClientNode {
    /// Creates a new [`RoughtimeClientNode`] instance, but does not start it.
    pub fn new(node_name: &str) -> Self {
        Self {
            node_name: node_name.to_string(),
        }
    }
}

impl super::Node for RoughtimeClientNode {
    fn run(
        self: Box<Self>,
        _runtime: RuntimeProxy,
        _handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        info!("{}: Starting Roughtime pseudo-Node", self.node_name);
        warn!("No Roughtime support implemented!");
    }
}
