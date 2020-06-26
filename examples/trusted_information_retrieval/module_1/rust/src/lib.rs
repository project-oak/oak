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

//! Database proxy Node for Project Oak.
//!
//! This shows how an Oak Node can privately retrieve information from an external database.
//!
//! In order to provide privacy while being able to request entries from the database, the following
//! scheme is implemented:
//! - The module receives a request for a specific database entry specified by key.
//! - Starts continuously requesting chunks of data from the database.
//! - Processes them and finds the requested entry.
//! - Sends a response only when all chunks have been requested from the database (even though it
//!   might have found the requested value earlier).
//!
//! This is necessary so we will not leak information about a particular chunk that contains the
//! requested entry, since an attacker could analyse network traffic.

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.database.rs"));
}

use anyhow::{anyhow, Context};
use oak::grpc;
use oak_abi::label::Label;
pub use proto::DatabaseProxyClient;
use proto::{
    DatabaseClient, DatabaseEntry, DatabaseProxy, DatabaseProxyDispatcher, GetDatabaseEntryRequest,
    GetDatabaseEntryResponse, ListDatabaseEntriesRequest,
};

const MODULE_CONFIG_NAME: &str = "database_proxy";
const MODULE_ENTRYPOINT_NAME: &str = "database_proxy_main";

/// Expected number of database entries per request.
const DATABASE_PAGE_SIZE: u32 = 5;

pub fn get_database_entry(id: &str, database_url: &str) -> grpc::Result<DatabaseEntry> {
    let client = oak::grpc::client::Client::new_with_label(
        &oak::node_config::wasm(MODULE_CONFIG_NAME, MODULE_ENTRYPOINT_NAME),
        &Label::public_untrusted(),
    )
    .map(DatabaseProxyClient)
    .ok_or_else(|| {
        grpc::build_status(
            grpc::Code::Unavailable,
            "Couldn't create database proxy Node",
        )
    })?;

    let request = GetDatabaseEntryRequest {
        key: id.to_string(),
        database_url: database_url.to_string(),
    };
    client.get_database_entry(request).and_then(|response| {
        response
            .entry
            .ok_or_else(|| grpc::build_status(grpc::Code::Internal, "Malformed response"))
    })
}

/// Oak Node that connects to an external database.
#[derive(Default)]
pub struct DatabaseProxyNode;

impl DatabaseProxyNode {
    /// Create a gRPC client pseudo-Node.
    fn get_grpc_client(database_url: &str) -> anyhow::Result<DatabaseClient> {
        oak::grpc::client::Client::new_with_label(
            &oak::node_config::grpc_client(database_url),
            &Label::public_untrusted(),
        )
        .map(DatabaseClient)
        .context("Couldn't create gRPC client")
    }

    /// Load a database subset defined by `offset` and the number of requested elements
    /// (`page_size`).
    fn list_database_entries(
        offset: u32,
        page_size: u32,
        database_url: &str,
    ) -> anyhow::Result<Vec<DatabaseEntry>> {
        let request = ListDatabaseEntriesRequest {
            offset: offset as i32,
            page_size: page_size as i32,
        };
        Self::get_grpc_client(database_url)?
            .list_database_entries(request)
            .map(|response| response.entries)
            .map_err(|error| anyhow!("gRPC send error: {:?}", error))
    }
}

/// A gRPC service implementation for the database proxy Node.
impl DatabaseProxy for DatabaseProxyNode {
    fn get_database_entry(
        &mut self,
        request: GetDatabaseEntryRequest,
    ) -> grpc::Result<GetDatabaseEntryResponse> {
        // Request entries from the database until the last entry page is reached.
        let mut requested_entry = None;
        let mut current_offset = 0;
        loop {
            let entries = Self::list_database_entries(
                current_offset,
                DATABASE_PAGE_SIZE,
                &request.database_url,
            )
            .map_err(|error| {
                grpc::build_status(
                    grpc::Code::NotFound,
                    // &format!("Database error: {:?}", error)[..],
                    format!("Database error: {:?}", error).as_ref(),
                )
            })?;

            // When the requested entry is found, we continue requesting new database entries, so
            // the database doesn't learn, which entry was requested.
            if let Some(entry) = entries.iter().find(|e| e.key == request.key) {
                requested_entry = Some(entry.clone());
            }

            // If the response contains fewer entries than requested, then it's the last database
            // page.
            if entries.len() < DATABASE_PAGE_SIZE as usize {
                break;
            }
            current_offset += DATABASE_PAGE_SIZE;
        }

        requested_entry
            .map(|entry| GetDatabaseEntryResponse { entry: Some(entry) })
            .ok_or_else(|| grpc::build_status(grpc::Code::NotFound, ""))
    }
}

oak::entrypoint!(database_proxy_main => |in_channel| {
    oak::logger::init_default();
    let dispatcher = DatabaseProxyDispatcher::new(DatabaseProxyNode::default());
    oak::run_event_loop(dispatcher, in_channel);
});
