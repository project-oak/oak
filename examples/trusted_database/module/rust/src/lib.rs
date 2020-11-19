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

//! Trusted Database example for Project Oak.
//!
//! This shows how an Oak Node can host an in-memory database and process private queries from
//! clients.
//!
//! Current example implementation uses a list of Santander Cycles in London as test database:
//! https://tfl.gov.uk/tfl/syndication/feeds/cycle-hire/livecyclehireupdates.xml
//!
//! Trusted Database example consists of two Oak Nodes: Main Node and Handler Node.
//!
//! Upon receiving a client request, Main Node creates a new dedicated Handler Node and proxies
//! the request to it. Main Node also contains the database of Points Of Interest and shares it with
//! all newly created Handler Nodes.
//!
//! The key idea is that clients don't need to trust any particular Wasm module and only need to
//! trust in the Oak implementation. Thus clients don't need to use module hash or module signature
//! labels and can only assign their token labels to the data.

pub mod proto {
    pub mod oak {
        pub use oak::proto::oak::invocation;
        pub use oak_services::proto::oak::log;
        pub mod examples {
            pub mod trusted_database {
                include!(concat!(
                    env!("OUT_DIR"),
                    "/oak.examples.trusted_database.rs"
                ));
                include!(concat!(
                    env!("OUT_DIR"),
                    "/oak.examples.trusted_database_init.rs"
                ));
            }
        }
    }
}

mod database;
mod handler;
mod router;
#[cfg(test)]
mod tests;

use crate::{proto::oak::examples::trusted_database::TrustedDatabaseInit, router::Router};
use anyhow::Context;
use database::load_database;
use oak::proto::oak::application::ConfigMap;
use oak_abi::label::Label;

/// Main entrypoint of the Trusted Database application.
///
/// This node is in charge of creating the other top-level nodes, but does not process any request.
#[derive(Default)]
struct Main;

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, config_map: Self::Command) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        oak::logger::init(log_sender.clone(), log::Level::Debug)?;
        let points_of_interest = load_database(config_map).expect("Couldn't load database");

        let init = TrustedDatabaseInit {
            log_sender: Some(log_sender),
            points_of_interest: Some(points_of_interest),
        };
        let router_sender = oak::io::entrypoint_node_create::<Router, _, _>(
            "router",
            &Label::public_untrusted(),
            "app",
            init,
        )
        .context("Couldn't create router node")?;
        oak::grpc::server::init_with_sender("[::]:8080", router_sender)
            .context("Couldn't create gRPC server pseudo-Node")?;
        Ok(())
    }
}

oak::entrypoint_command_handler!(oak_main => Main);
