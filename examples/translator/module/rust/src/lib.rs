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
use oak::grpc;
use oak::grpc::OakNode;
use oak_derive::OakExports;
use translator_common::proto::translator::{TranslateRequest, TranslateResponse};
use translator_common::proto::translator_grpc::{dispatch, TranslatorNode};

#[derive(OakExports)]
struct Node {}

impl OakNode for Node {
    fn new() -> Self {
        oak_log::init_default();
        Node {}
    }
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}

impl TranslatorNode for Node {
    fn translate(&mut self, req: TranslateRequest) -> grpc::Result<TranslateResponse> {
        info!(
            "attempt to translate '{}' from {} to {}",
            req.text, req.from_lang, req.to_lang
        );
        let mut rsp = TranslateResponse::new();
        rsp.translated_text = match req.from_lang.as_str() {
            "en" => match req.text.as_str() {
                "WORLDS" => match req.to_lang.as_str() {
                    "fr" => "MONDES".to_string(),
                    "it" => "MONDI".to_string(),
                    _ => {
                        info!("output language {} not found", req.to_lang);
                        return Err(grpc::build_status(
                            grpc::Code::NOT_FOUND,
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
                        grpc::Code::NOT_FOUND,
                        "Input text unrecognized",
                    ));
                }
            },
            _ => {
                info!("input language '{}' not recognized", req.from_lang);
                return Err(grpc::build_status(
                    grpc::Code::NOT_FOUND,
                    "Input language unrecognized",
                ));
            }
        };
        info!("translation '{}'", rsp.translated_text);
        Ok(rsp)
    }
}
