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

//! Aggregator example for Project Oak.
//!
//! This shows how an Oak Node can aggregate data samples and report aggregated
//! values if there are enough samples to hide individual contributors (enforces
//! k-anonymity).
//!
//! Clients invoke the module by providing data samples that contain a bucket ID
//! and a Sparse Vector - a dictionary with integer keys.

pub mod router;

use crate::router::Router;
use aggregator_handler::{
    proto::oak::examples::aggregator::{HandlerInit, RouterInit},
    Handler,
};
use anyhow::Context;
use log::info;
use oak::{
    io::Sender,
    proto::oak::{application::ConfigMap, invocation::GrpcInvocationSender},
};
use oak_abi::label::{confidentiality_label, web_assembly_module_tag, Label};
use oak_services::proto::oak::log::LogMessage;

#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    pub grpc_server_listen_address: String,
    pub backend_server_address: String,
}

// SHA-256 hash of Handler module.
// Used to assign a confidentiality label to Handler Node, and to check client request labels.
const HANDLER_SHA256_HASH: &str =
    "e809f4274d336e96c93c0c20486f89b5894a63ec2e5461c9534696516570942c";

/// Main entrypoint of the Aggregator application.
///
/// This node is in charge of creating the other top-level nodes, but does not process any request.
#[derive(Default)]
struct Main;

impl Main {
    fn create_router(
        grpc_server_listen_address: &str,
        log_sender: Sender<LogMessage>,
        handler_invocation_sender: Sender<oak::grpc::Invocation>,
    ) -> anyhow::Result<()> {
        let init = RouterInit {
            log_sender: Some(log_sender),
            handler_invocation_sender: Some(GrpcInvocationSender {
                sender: Some(handler_invocation_sender),
            }),
        };
        let router_sender = oak::io::entrypoint_node_create::<Router, _, _>(
            "router",
            &Label::public_untrusted(),
            "app",
            init,
        )
        .context("Couldn't create router node")?;
        oak::grpc::server::init_with_sender(grpc_server_listen_address, router_sender)
            .context("Couldn't create gRPC server pseudo-Node")?;
        Ok(())
    }

    fn create_handler(
        log_sender: Sender<LogMessage>,
        grpc_client_invocation_sender: Sender<oak::grpc::Invocation>,
    ) -> anyhow::Result<Sender<oak::grpc::Invocation>> {
        // Create an Handler Node.
        let aggregator_hash_label = confidentiality_label(web_assembly_module_tag(
            &hex::decode(HANDLER_SHA256_HASH).context("Couldn't decode SHA-256 hex value")?,
        ));

        // Send the initialization message to Handler Node containing a gRPC server invocation
        // receiver and a gRPC client invocation sender.
        let init_message = HandlerInit {
            log_sender: Some(log_sender),
            grpc_client_invocation_sender: Some(GrpcInvocationSender {
                sender: Some(grpc_client_invocation_sender),
            }),
        };
        oak::io::entrypoint_node_create::<Handler, _, _>(
            "handler",
            &aggregator_hash_label,
            "handler",
            init_message,
        )
        .map_err(|err| err.into())
    }
}

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, command: ConfigMap) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        oak::logger::init(log_sender.clone(), log::Level::Debug)?;
        let config: Config =
            toml::from_slice(&command.items.get("config").expect("Couldn't find config"))
                .context("Couldn't parse TOML config file")?;
        info!("Parsed config: {:?}", config);

        // Create Oak Nodes.
        let grpc_client_invocation_sender = oak::grpc::client::init(&config.backend_server_address)
            .context("Couldn't create gRPC client")?;
        let handler_invocation_sender =
            Self::create_handler(log_sender.clone(), grpc_client_invocation_sender)?;
        Self::create_router(
            &config.grpc_server_listen_address,
            log_sender,
            handler_invocation_sender,
        )
    }
}

oak::entrypoint_command_handler!(oak_main => Main);
