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
    include!(concat!(env!("OUT_DIR"), "/examples.translator.rs"));
}

use log::{info, warn};
use oak_services::proto::oak::log::LogInit;
use proto::TranslateRequest;
pub use proto::TranslatorClient;

pub fn translate(
    client: &TranslatorClient,
    text: &str,
    from_lang: &str,
    to_lang: &str,
) -> Option<String> {
    info!(
        "attempt to translate '{}' from {} to {}",
        text, from_lang, to_lang
    );
    let req = TranslateRequest {
        text: text.to_string(),
        from_lang: from_lang.to_string(),
        to_lang: to_lang.to_string(),
    };

    match client.translate(req) {
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

/// Stub with a manual implementation of [`oak::WasmEntrypoint`], to be used by other nodes that
/// want to instantiate a translator node. The manual implementation must be kept in sync with the
/// auto-generated implementation from the translator module.
pub struct TranslatorEntrypoint;

impl oak::WasmEntrypoint for TranslatorEntrypoint {
    const ENTRYPOINT_NAME: &'static str = "handler";
    type Message = oak_io::InitWrapper<LogInit, oak::grpc::Invocation>;
}
