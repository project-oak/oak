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

mod proto;
#[cfg(test)]
mod tests;

use log::{info, warn};
use oak::grpc;
use oak::grpc::OakNode;
use oak_derive::OakExports;
use proto::hello_world::{HelloRequest, HelloResponse};
use proto::hello_world_grpc::{dispatch, HelloWorld};

#[derive(OakExports)]
struct Node {
    storage: Option<oak::storage::Storage>,
    translator: Option<translator_common::TranslatorClient>,
}

impl Node {
    fn translate(&self, text: &str, from_lang: &str, to_lang: &str) -> Option<String> {
        let client = self.translator.as_ref()?;
        translator_common::translate(client, text, from_lang, to_lang)
    }
}

const STORAGE_NAME: &[u8] = b"HelloWorld";
const FIELD_NAME: &[u8] = b"last-greeting";

impl OakNode for Node {
    fn new() -> Self {
        oak_log::init_default();
        Node {
            storage: oak::storage::Storage::default(),
            translator: grpc::client::Client::new("translator", "oak_main")
                .map(translator_common::TranslatorClient),
        }
    }
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}

impl HelloWorld for Node {
    fn say_hello(&mut self, req: HelloRequest) -> grpc::Result<HelloResponse> {
        if req.greeting == "Query-of-Error" {
            return Err(grpc::build_status(
                grpc::Code::INVALID_ARGUMENT,
                "Deliberate error",
            ));
        }
        // Save the latest greeting to storage.
        if let Some(storage) = &mut self.storage {
            match storage.write(STORAGE_NAME, FIELD_NAME, req.greeting.as_bytes()) {
                Ok(_) => {}
                Err(status) => warn!(
                    "failed to store last greeting: code={} {}",
                    status.code, status.message
                ),
            }
        }
        info!("Say hello to {}", req.greeting);
        let mut res = HelloResponse::new();
        res.reply = format!("HELLO {}!", req.greeting);
        Ok(res)
    }

    fn lots_of_replies(&mut self, req: HelloRequest, mut writer: grpc::ChannelResponseWriter) {
        info!("Say hello to {}", req.greeting);
        let mut res1 = HelloResponse::new();
        res1.reply = format!("HELLO {}!", req.greeting);
        writer
            .write(&res1, grpc::WriteMode::KeepOpen)
            .expect("Failed to write response");

        // Also generate a response with the last-stored value.
        let previous = if let Some(storage) = &mut self.storage {
            let result = storage.read(STORAGE_NAME, FIELD_NAME);
            match result {
                Ok(v) => String::from_utf8(v).unwrap(),
                Err(status) => {
                    warn!(
                        "Failed to find previous value: code={} {}",
                        status.code, status.message
                    );
                    "<default>".to_string()
                }
            }
        } else {
            "<default>".to_string()
        };
        // Attempt to also generate a translated response.
        if let Some(salutation) = self.translate(&req.greeting, "en", "fr") {
            info!("Say bonjour to {}", salutation);
            let mut res = HelloResponse::new();
            res.reply = format!("BONJOUR {}!", salutation);
            writer
                .write(&res, grpc::WriteMode::KeepOpen)
                .expect("Failed to write translated response");
        }

        info!("Say hello again to {}", previous);
        let mut res2 = HelloResponse::new();
        res2.reply = format!("HELLO AGAIN {}!", previous);
        writer
            .write(&res2, grpc::WriteMode::Close)
            .expect("Failed to write final response");
    }

    fn lots_of_greetings(&mut self, reqs: Vec<HelloRequest>) -> grpc::Result<HelloResponse> {
        info!("Say hello");
        let mut msg = String::new();
        msg.push_str("Hello ");
        msg.push_str(&recipients(&reqs));
        let mut res = HelloResponse::new();
        res.reply = msg;
        Ok(res)
    }

    fn bidi_hello(&mut self, reqs: Vec<HelloRequest>, mut writer: grpc::ChannelResponseWriter) {
        info!("Say hello");
        let msg = recipients(&reqs);
        let mut res1 = HelloResponse::new();
        res1.reply = format!("HELLO {}!", msg);
        writer
            .write(&res1, grpc::WriteMode::KeepOpen)
            .expect("Failed to write response");
        let mut res2 = HelloResponse::new();
        res2.reply = format!("BONJOUR {}!", msg);
        writer
            .write(&res2, grpc::WriteMode::Close)
            .expect("Failed to write final response");
    }
}

fn recipients(reqs: &[HelloRequest]) -> String {
    let mut result = String::new();
    for (i, req) in reqs.iter().enumerate() {
        if i > 0 {
            result.push_str(", ");
        }
        result.push_str(&req.greeting);
    }
    result
}
