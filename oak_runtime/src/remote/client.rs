//
// Copyright 2021 The Project Oak Authors
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

//! Functionality for remote runtime clients.

use crate::proto::oak::remote::remote_runtime_client::RemoteRuntimeClient;
use std::collections::HashSet;
use tonic::transport::Channel;

#[derive(Default)]
pub struct RemoteClients {
    /// Set of known remote runtime addresses
    clients: HashSet<String>,
}

impl RemoteClients {
    pub fn add_remote(&mut self, remote_addr: String) {
        self.clients.insert(remote_addr);
    }

    #[allow(dead_code)]
    pub async fn get_client(
        &self,
        remote_addr: String,
    ) -> anyhow::Result<RemoteRuntimeClient<Channel>> {
        if self.clients.contains(&remote_addr) {
            let channel = Channel::from_shared(remote_addr.to_owned())?
                .connect()
                .await?;
            Ok(RemoteRuntimeClient::new(channel))
        } else {
            Err(anyhow::anyhow!("Could not find remote with the given id"))
        }
    }
}
