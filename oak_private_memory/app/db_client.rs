//
// Copyright 2025 The Project Oak Authors
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
use std::net::SocketAddr;

use anyhow::bail;
use log::info;
use metrics::get_global_metrics;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use tokio::sync::RwLock;
use tonic::transport::{Channel, Endpoint};
const MAX_CONNECT_RETRIES: usize = 5;
const INITIAL_BACKOFF_MS: u64 = 100;
pub const MAX_DECODE_SIZE: usize = 100 * 1024 * 1024; // 100 MB

pub struct SharedDbClient {
    database_service_host: SocketAddr,
    client: RwLock<Option<SealedMemoryDatabaseServiceClient<Channel>>>,
}

impl SharedDbClient {
    pub fn new(database_service_host: SocketAddr) -> Self {
        Self { database_service_host, client: RwLock::new(None) }
    }

    pub async fn get_or_connect(
        &self,
    ) -> anyhow::Result<SealedMemoryDatabaseServiceClient<Channel>> {
        // First, try to get a read lock and check if the client is already initialized.
        {
            let read_guard = self.client.read().await;
            if let Some(client) = read_guard.as_ref() {
                info!("Reusing cached DB client");
                return Ok(client.clone());
            }
        }

        // If the client is not initialized, get a write lock to initialize it.
        let mut write_guard = self.client.write().await;
        // Check again in case another thread initialized it while we were waiting for
        // the write lock.
        if let Some(client) = write_guard.as_ref() {
            info!("Reusing cached DB client initialized by another thread");
            return Ok(client.clone());
        }

        let mut backoff = INITIAL_BACKOFF_MS;
        let db_addr = self.database_service_host;
        let db_url = format!("http://{db_addr}");
        info!("Database service URL: {}", db_url);
        let endpoint = Endpoint::from_shared(db_url.clone())?;
        for attempt in 0..MAX_CONNECT_RETRIES {
            info!("Creating new DB client, attempt {}", attempt + 1);

            match endpoint.connect().await {
                Ok(channel) => {
                    let new_client = SealedMemoryDatabaseServiceClient::new(channel)
                        .max_decoding_message_size(MAX_DECODE_SIZE);
                    *write_guard = Some(new_client.clone());
                    info!("Successfully created and cached new DB client");
                    return Ok(new_client);
                }
                Err(err) => {
                    info!("Failed to connect to database service: {}", err);
                }
            }

            tokio::time::sleep(tokio::time::Duration::from_millis(backoff)).await;
            backoff *= 2;
            get_global_metrics().inc_db_connect_retries();
        }
        bail!("Failed to connect to database service after {} attempts", MAX_CONNECT_RETRIES);
    }
}
