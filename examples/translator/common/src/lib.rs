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

pub mod proto;

use log::{info, warn};
use proto::translator::{TranslateRequest, TranslateResponse};

/// Client for a translator Node.
pub struct TranslatorClient {
    invocation_sender: oak::io::Sender<oak::grpc::Invocation>,
}

// TODO(#549): autogenerate most of this code based on the gRPC service definition.
impl TranslatorClient {
    /// Attempt to create a new translator Node and connection to it, assuming
    /// that the Wasm code for the translator Node is available under the given
    /// config name.  Returns `None` if it was not possible to create the
    /// translator.
    pub fn new(config_name: &str) -> Option<TranslatorClient> {
        let (invocation_sender, invocation_receiver) =
            oak::io::channel_create().expect("failed to create channel");
        let status = oak::node_create(config_name, "oak_main", invocation_receiver.handle);
        invocation_receiver
            .close()
            .expect("failed to close channel");
        match status {
            Ok(_) => {
                info!("translator client created");
                Some(TranslatorClient { invocation_sender })
            }
            Err(status) => {
                warn!("failed to create translator: {:?}", status);
                None
            }
        }
    }
    pub fn translate(&self, text: &str, from_lang: &str, to_lang: &str) -> Option<String> {
        info!(
            "attempt to translate '{}' from {} to {}",
            text, from_lang, to_lang
        );
        let mut req = TranslateRequest::new();
        req.text = text.to_string();
        req.from_lang = from_lang.to_string();
        req.to_lang = to_lang.to_string();

        let rsp: oak::grpc::Result<TranslateResponse> = oak::grpc::invoke_grpc_method(
            "/oak.examples.translator.Translator/Translate",
            req,
            &self.invocation_sender,
        );
        match rsp {
            Ok(rsp) => {
                info!("translation '{}'", rsp.translated_text);
                Some(rsp.translated_text)
            }
            Err(status) => {
                warn!(
                    "gRPC invocation failed: code {} msg {}",
                    status.code, status.message
                );
                None
            }
        }
    }
}
