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

#[cfg(test)]
mod tests;

use log::info;
use oak::grpc;
use translator_common::proto::{
    TranslateRequest, TranslateResponse, Translator, TranslatorDispatcher,
};

oak::entrypoint!(oak_main => {
    oak::logger::init_default();
    TranslatorDispatcher::new(Node)
});

oak::entrypoint_rust!(oak_main_rust => {
    oak::logger::init_default();
    let dispatcher = TranslatorDispatcher::new(Node);
    let grpc_channel = oak::grpc::server::init_default();
    oak::run_event_loop_impl(dispatcher, grpc_channel);
});

struct Node;

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
