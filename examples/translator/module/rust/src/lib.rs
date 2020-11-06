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

use log::info;
use oak::{
    grpc,
    io::{Receiver, ReceiverExt},
};
use oak_abi::proto::oak::application::ConfigMap;
use translator_common::proto::{
    TranslateRequest, TranslateResponse, Translator, TranslatorDispatcher,
};

// The `oak_main` entrypoint is used when the Translator acts as a library Node for a
// wider Application. In this case, invocations arrive directly over the channel received
// at start-of-day.
oak::entrypoint!(oak_main<grpc::Invocation> => |receiver: Receiver<grpc::Invocation>| {
    oak::logger::init_default();
    oak::run_command_loop(Node, receiver.iter());
});

// The `grpc_oak_main` entrypoint is used when the Translator acts as a standalone Oak
// Application. In this case, it creates a gRPC server pseudo-Node on startup, and
// invocations arrive from the outside world over the channel that connects with the
// pseudo-Node.
oak::entrypoint!(grpc_oak_main<ConfigMap> => |_receiver| {
    oak::logger::init_default();
    let grpc_channel =
        oak::grpc::server::init("[::]:8080").expect("could not create gRPC server pseudo-Node");
    oak::run_command_loop(Node, grpc_channel.iter());
});

struct Node;

oak::impl_dispatcher!(impl Node : TranslatorDispatcher);

impl Translator for Node {
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
