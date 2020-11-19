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
use oak::{grpc, Label};
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
        let handler_sender = oak::io::entrypoint_node_create::<Handler, _, _>(
            "handler",
            &Label::public_untrusted(),
            "app",
            LogInit {
                log_sender: Some(log_sender),
            },
        )
        .context("could not create handler node")?;
        oak::grpc::server::init_with_sender("[::]:8080", handler_sender)
            .context("could not create gRPC server pseudo-Node")?;
        Ok(())
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
            "attempt to translate '{}' from {} to {}",
            req.text, req.from_lang, req.to_lang
        );
        let mut rsp = TranslateResponse::default();
        rsp.translated_text = match req.from_lang.as_str() {
            "en" => match req.text.as_str() {
                "WORLDS" => match req.to_lang.as_str() {
                    "fr" => "MONDES".to_string(),
                    "it" => "MONDI".to_string(),
                    _ => {
                        info!("output language {} not found", req.to_lang);
                        return Err(grpc::build_status(
                            grpc::Code::NotFound,
                            "Output language not found",
                        ));
                    }
                },
                _ => {
                    info!(
                        "input text '{}' in {} not recognized",
                        req.text, req.from_lang
                    );
                    return Err(grpc::build_status(
                        grpc::Code::NotFound,
                        "Input text unrecognized",
                    ));
                }
            },
            _ => {
                info!("input language '{}' not recognized", req.from_lang);
                return Err(grpc::build_status(
                    grpc::Code::NotFound,
                    "Input language unrecognized",
                ));
            }
        };
        info!("translation '{}'", rsp.translated_text);
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
