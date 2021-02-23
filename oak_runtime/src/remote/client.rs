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
use std::collections::HashMap;
use tonic::transport::Channel;

#[derive(Default)]
pub struct RemoteClients {
    /// Map of remote runtime ids and their addresses
    clients: HashMap<String, String>,
}

impl RemoteClients {
    pub fn new() -> Self {
        RemoteClients {
            ..Default::default()
        }
    }

    pub fn add_remote(&mut self, remote_id: String, remote_addr: String) {
        self.clients.insert(remote_id, remote_addr);
    }

    pub async fn get_client(
        &self,
        remote_id: String,
    ) -> anyhow::Result<RemoteRuntimeClient<Channel>> {
        let remote_addr = self
            .clients
            .get(&remote_id)
            .ok_or_else(|| anyhow::anyhow!("Could not find remote with the given id"))?;

        let channel = Channel::from_shared(remote_addr.to_owned())?
            .connect()
            .await?;
        Ok(RemoteRuntimeClient::new(channel))
    }
}
