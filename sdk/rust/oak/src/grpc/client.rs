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

use log::{info, warn};

/// Client for a gRPC service in another Node.
pub struct Client {
    pub invocation_sender: crate::io::Sender<crate::grpc::Invocation>,
}

impl Client {
    /// Create a new Node that implements a gRPC service, and if successful return a Client.
    pub fn new(config_name: &str, entrypoint_name: &str) -> Option<Client> {
        let (invocation_sender, invocation_receiver) =
            crate::io::channel_create().expect("failed to create channel");
        let status = crate::node_create(config_name, entrypoint_name, invocation_receiver.handle);
        invocation_receiver
            .close()
            .expect("failed to close channel");
        match status {
            Ok(_) => {
                info!(
                    "Client created for '{}' in '{}'",
                    entrypoint_name, config_name
                );
                Some(Client { invocation_sender })
            }
            Err(status) => {
                warn!(
                    "failed to create Client for '{}' in '{}' : {:?}",
                    entrypoint_name, config_name, status
                );
                None
            }
        }
    }
}
