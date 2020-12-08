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

pub mod proto {
    pub mod oak {
        pub use oak::proto::oak::invocation;
        pub use oak_services::proto::oak::log;
        pub mod examples {
            pub mod treehouse {
                include!(concat!(env!("OUT_DIR"), "/oak.examples.treehouse.rs"));
                include!(concat!(env!("OUT_DIR"), "/oak.examples.treehouse_init.rs"));
            }
        }
    }
}

mod handler;
mod router;

use crate::{proto::oak::examples::treehouse::TreehouseRouterInit, router::Router};
use anyhow::Context;
use oak::proto::oak::application::ConfigMap;
use oak_abi::label::Label;

#[derive(Default)]
struct Main;

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, config_map: Self::Command) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        oak::logger::init(log_sender.clone(), log::Level::Debug)?;
        let oauth2_token = String::from_utf8(
            config_map
                .items
                .get("config")
                .context("Couldn't find config")?
                .to_vec(),
        )
        .context("Couldn't parse token string")?;

        let init = TreehouseRouterInit {
            log_sender: Some(log_sender),
            oauth2_token,
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
