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

//! Database example implementation for the Trusted Information Retrieval example.
//!
//! Database recieves gRPC requests from Oak and sends database subsets in response.
//! Database is updated every minute.
//!
//! Current example implementation uses a list of Santander Cycles in London as test database:
//! https://tfl.gov.uk/tfl/syndication/feeds/cycle-hire/livecyclehireupdates.xml

mod database;
mod proto {
    tonic::include_proto!("oak.examples.database");
    tonic::include_proto!("oak.examples.trusted_information_retrieval");
}
#[cfg(test)]
mod tests;

use database::load_database;
use futures::future::FutureExt;
use log::{error, info};
use prost::Message;
use proto::{
    database_server::{Database, DatabaseServer},
    DatabaseEntry, ListDatabaseEntriesRequest, ListDatabaseEntriesResponse, PointOfInterest,
};
use reqwest::Url;
use std::sync::Arc;
use structopt::StructOpt;
use tokio::sync::Mutex;
use tonic::{
    transport::{Identity, Server, ServerTlsConfig},
    Request, Response, Status,
};

#[derive(StructOpt, Clone)]
#[structopt(about = "Aggregator Backend")]
pub struct Opt {
    #[structopt(long, help = "Private RSA key file used by gRPC server")]
    grpc_tls_private_key: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 TLS certificate file used by gRPC server"
    )]
    grpc_tls_certificate: String,
    #[structopt(
        long,
        help = "Database URL",
        default_value = "https://tfl.gov.uk/tfl/syndication/feeds/cycle-hire/livecyclehireupdates.xml"
    )]
    database_url: String,
}

pub struct DatabaseService {
    entries: Arc<Mutex<Vec<PointOfInterest>>>,
}

#[tonic::async_trait]
impl Database for DatabaseService {
    async fn list_database_entries(
        &self,
        request: Request<ListDatabaseEntriesRequest>,
    ) -> Result<Response<ListDatabaseEntriesResponse>, Status> {
        let offset = request.get_ref().offset as usize;
        let page_size = request.get_ref().page_size as usize;
        let database_entries = self.entries.lock().await;

        // Copy requested database entries.
        let requested_entries = if offset + page_size < database_entries.len() {
            database_entries[offset..offset + page_size].to_vec()
        } else {
            database_entries[offset..].to_vec()
        };

        let response = ListDatabaseEntriesResponse {
            entries: requested_entries
                .iter()
                .map(|entry| {
                    // Serialize database entry in a String.
                    let mut serialized_entry = Vec::new();
                    entry.encode(&mut serialized_entry).unwrap();
                    DatabaseEntry {
                        key: entry.id.to_string(),
                        value: serialized_entry,
                    }
                })
                .collect(),
        };
        Ok(Response::new(response))
    }
}

/// Loop for requesting a new database version from `url`.
async fn update_database_loop(url: Url, database: Arc<Mutex<Vec<PointOfInterest>>>) {
    loop {
        info!("Updating database");
        match load_database(url.clone()).await {
            Ok(updated_database_entries) => {
                let mut database_entries = database.lock().await;
                *database_entries = updated_database_entries;
            }
            Err(error) => error!("Error loading database: {:?}", error),
        }

        // Wait for a minute before updating the database.
        tokio::time::delay_for(tokio::time::Duration::from_secs(60)).await;
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();
    info!("Running backend database");

    let private_key = tokio::fs::read(&opt.grpc_tls_private_key).await?;
    let certificate = tokio::fs::read(&opt.grpc_tls_certificate).await?;
    let database_url = Url::parse(&opt.database_url).expect("Couldn't parse database URL");

    // Create a mutex-protected database.
    let database = Arc::new(Mutex::new(vec![]));

    // Run a separate asynchronous task for updating the database.
    tokio::spawn(update_database_loop(database_url, database.clone()));

    let handler = DatabaseService { entries: database };

    let identity = Identity::from_pem(certificate, private_key);
    let address = "[::]:8888".parse()?;

    info!("Starting gRPC server at {:?}", address);
    Server::builder()
        .tls_config(ServerTlsConfig::new().identity(identity))
        .expect("Couldn't create TLS configuration")
        .add_service(DatabaseServer::new(handler))
        .serve_with_shutdown(address, tokio::signal::ctrl_c().map(|r| r.unwrap()))
        .await?;

    Ok(())
}
