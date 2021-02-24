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

pub mod proto {
    pub mod oak {
        pub use oak::proto::oak::invocation;
        pub use oak_services::proto::oak::log;
        pub mod examples {
            pub mod proxy_attestation {
                include!(concat!(
                    env!("OUT_DIR"),
                    "/oak.examples.proxy_attestation_example.rs"
                ));
            }
        }
    }
}

use crate::proto::oak::examples::proxy_attestation::{
    ExampleApplication, ExampleApplicationDispatcher, GetExampleMessageRequest,
    GetExampleMessageResponse,
};
use anyhow::Context;
use log::info;
use oak::{grpc, Label};
use oak_abi::proto::oak::application::ConfigMap;
use oak_services::proto::oak::log::LogInit;

// Example message to send to the client.
const EXAMPLE_MESSAGE: &str = "Example message";

oak::entrypoint_command_handler!(oak_main => Main);

#[derive(Default)]
struct Main;

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: ConfigMap) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        oak::logger::init(log_sender.clone(), log::Level::Debug)?;

        let handler_command_sender = oak::io::entrypoint_node_create::<Handler, _, _>(
            "handler",
            &Label::public_untrusted(),
            "app",
            LogInit {
                log_sender: Some(log_sender),
            },
        )
        .context("Couldn't create handler node")?;

        oak::grpc::server::init_with_sender("[::]:8080", handler_command_sender)
            .context("Couldn't create gRPC server pseudo-Node")?;
        Ok(())
    }
}

oak::impl_dispatcher!(impl Handler : ExampleApplicationDispatcher);
oak::entrypoint_command_handler_init!(handler => Handler);

#[derive(Default)]
pub struct Handler;

impl oak::WithInit for Handler {
    type Init = LogInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        Self::default()
    }
}

impl ExampleApplication for Handler {
    fn get_example_message(
        &mut self,
        _req: GetExampleMessageRequest,
    ) -> grpc::Result<GetExampleMessageResponse> {
        info!("Received request");
        Ok(GetExampleMessageResponse {
            message: EXAMPLE_MESSAGE.to_string(),
        })
    }
}
