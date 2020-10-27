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

use crate::io::{ReceiverExt, SenderExt};
use log::{info, warn};
use oak_abi::{label::Label, proto::oak::application::NodeConfiguration};

/// Client for a gRPC service in another Node.
pub struct Client {
    pub invocation_sender: crate::io::Sender<crate::grpc::Invocation>,
}

impl Client {
    /// Similar to [`Client::new_with_label`] but with a fixed label corresponding to "public
    /// untrusted".
    pub fn new(config: &NodeConfiguration) -> Option<Client> {
        Client::new_with_label(config, &Label::public_untrusted())
    }

    /// Creates a new Node that implements a gRPC service, and if successful return a Client.
    ///
    /// The config name specifies the Node configuration that provides the service; the
    /// entrypoint name is required if this specifies another WebAssembly Oak Node, but is
    /// ignored if the Node configuration is for a gRPC client pseudo-Node (which acts as a
    /// proxy for a remote non-Oak gRPC service).
    ///
    /// The provided [`Label`] specifies the label for the newly created Node and Channel.
    pub fn new_with_label(config: &NodeConfiguration, label: &Label) -> Option<Client> {
        let (invocation_sender, invocation_receiver) =
            crate::io::channel_create(label).expect("failed to create channel");
        let status = crate::node_create_with_label(config, label, invocation_receiver.handle);
        invocation_receiver
            .close()
            .expect("failed to close channel");
        match status {
            Ok(_) => {
                info!(
                    "Client created for '{:?}', accessible via channel {:?}",
                    config, invocation_sender.handle
                );
                Some(Client { invocation_sender })
            }
            Err(status) => {
                warn!("failed to create Client for '{:?}': {:?}", config, status);
                None
            }
        }
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        info!("Closing Client channel {:?}", self.invocation_sender.handle);
        if let Err(status) = self.invocation_sender.close() {
            warn!(
                "Failed to close Client channel {:?}: {:?}",
                self.invocation_sender.handle, status
            );
        }
    }
}
