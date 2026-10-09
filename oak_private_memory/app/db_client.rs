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
use std::{net::SocketAddr, sync::Arc};

use anyhow::bail;
use log::info;
use metrics::Metrics;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use tokio::sync::RwLock;
use tonic::transport::{Channel, Endpoint};

const MAX_CONNECT_RETRIES: usize = 5;
const INITIAL_BACKOFF_MS: u64 = 100;

pub struct SharedDbClient {
    database_service_host: SocketAddr,
    max_grpc_decode_size: usize,
    client: RwLock<Option<SealedMemoryDatabaseServiceClient<Channel>>>,
    metrics: Arc<Metrics>,
}

impl SharedDbClient {
    pub fn new(
        database_service_host: SocketAddr,
        max_grpc_decode_size: usize,
        metrics: Arc<Metrics>,
    ) -> Self {
        Self { database_service_host, max_grpc_decode_size, client: RwLock::new(None), metrics }
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
                        .max_decoding_message_size(self.max_grpc_decode_size);
                    *write_guard = Some(new_client.clone());
                    info!("Successfully created and cached new DB client");
                    return Ok(new_client);
                }
                Err(err) => {
                    info!("Failed to connect to database service: {}", err);
                }
            }

            self.metrics.inc_db_connect_retries();
            tokio::time::sleep(tokio::time::Duration::from_millis(backoff)).await;
            backoff *= 2;
        }
        bail!("Failed to connect to database service after {} attempts", MAX_CONNECT_RETRIES);
    }
}

#[cfg(test)]
mod tests {
    use oak_private_memory_database::database::MAX_GRPC_DECODE_SIZE;

    use super::*;

    #[tokio::test]
    async fn connect_failure_counts_retries() {
        let harness = metrics_testing::TestMetrics::new(Metrics::new);
        // Reserve a free port and release it, so that nothing listens there.
        let closed_port_addr =
            std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap();
        // The decode size doesn't matter: no connection is ever made.
        let client =
            SharedDbClient::new(closed_port_addr, MAX_GRPC_DECODE_SIZE, harness.metrics.clone());

        assert!(client.get_or_connect().await.is_err());

        // Every failed connection attempt is counted, including the last one.
        assert_eq!(
            harness.collect().counter("db_connect_retries", &[]),
            MAX_CONNECT_RETRIES as u64
        );
    }
}
