//
// Copyright 2018 The Project Oak Authors
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

use anyhow::Context;
use log::info;
use oak::{
    grpc,
    io::{ReceiverExt, SenderExt},
    CommandHandler, Label,
};
use oak_abi::proto::oak::application::ConfigMap;
use oak_services::proto::oak::log::LogInit;
use translator_common::proto::{
    TranslateRequest, TranslateResponse, Translator, TranslatorDispatcher,
};

oak::entrypoint_command_handler!(oak_main => Main);

#[derive(Default)]
struct Main;

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: ConfigMap) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        let router_sender = oak::io::entrypoint_node_create::<Router, _, _>(
            "router",
            &Label::public_untrusted(),
            "app",
            LogInit {
                log_sender: Some(log_sender),
            },
        )
        .context("Couldn't create router node")?;
        oak::grpc::server::init_with_sender("[::]:8080", router_sender)
            .context("Couldn't create gRPC server pseudo-Node")?;
        Ok(())
    }
}

oak::entrypoint_command_handler_init!(router => Router);

#[derive(Default)]
pub struct Router {
    /// Saved init message to be sent to Handler Node.
    init: LogInit,
}

impl oak::WithInit for Router {
    type Init = LogInit;

    fn create(init: Self::Init) -> Self {
        Self { init }
    }
}

/// Creates individual Handler Nodes for each client request and assigns client labels to them.
impl CommandHandler for Router {
    type Command = grpc::Invocation;

    fn handle_command(&mut self, invocation: Self::Command) -> anyhow::Result<()> {
        let label = invocation
            .receiver
            .as_ref()
            .context("Couldn't get receiver")?
            .label()
            .context("Couldn't get label")?;
        let handler_invocation_sender = oak::io::entrypoint_node_create::<Handler, _, _>(
            "handler",
            &label,
            "app",
            self.init.clone(),
        )
        .context("Couldn't create handler node")?;
        let ret = handler_invocation_sender
            .send(&invocation)
            .context("Couldn't send invocation to handler node");
        invocation.close()?;
        ret
    }
}

// The `handler` entrypoint is also used when the Translator acts as a library Node for a wider
// Application. In this case, invocations arrive directly over the channel received at start-of-day.
oak::entrypoint_command_handler_init!(handler => Handler);
oak::impl_dispatcher!(impl Handler : TranslatorDispatcher);

#[derive(Default)]
struct Handler;

impl Translator for Handler {
    fn translate(&mut self, req: TranslateRequest) -> grpc::Result<TranslateResponse> {
        info!(
            "Attempt to translate '{}' from {} to {}",
            req.text, req.from_lang, req.to_lang
        );
        let rsp = TranslateResponse {
            translated_text: match req.from_lang.as_str() {
                "en" => match req.text.as_str() {
                    "WORLDS" => match req.to_lang.as_str() {
                        "fr" => "MONDES".to_string(),
                        "it" => "MONDI".to_string(),
                        _ => {
                            info!("Output language {} not found", req.to_lang);
                            return Err(grpc::build_status(
                                grpc::Code::NotFound,
                                "Output language not found",
                            ));
                        }
                    },
                    _ => {
                        info!(
                            "Input text '{}' in {} not recognized",
                            req.text, req.from_lang
                        );
                        return Err(grpc::build_status(
                            grpc::Code::NotFound,
                            "Input text unrecognized",
                        ));
                    }
                },
                _ => {
                    info!("Input language '{}' not recognized", req.from_lang);
                    return Err(grpc::build_status(
                        grpc::Code::NotFound,
                        "Input language unrecognized",
                    ));
                }
            },
        };
        info!("Translation '{}'", rsp.translated_text);
        Ok(rsp)
    }
}

impl oak::WithInit for Handler {
    type Init = LogInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        Self::default()
    }
}
