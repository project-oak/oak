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

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.hello_world.rs"));
}

use either::Either;
use log::info;
use oak::grpc;
use oak_abi::{label::Label, proto::oak::application::ConfigMap};
use oak_io::Sender;
use proto::{HelloRequest, HelloResponse, HelloWorld, HelloWorldDispatcher};

#[derive(Default)]
struct Main;

oak::entrypoint_command_handler!(oak_main => Main);

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: Self::Command) -> anyhow::Result<()> {
        let translator_sender_result = oak::io::node_create::<grpc::Invocation>(
            "translator",
            &Label::public_untrusted(),
            &oak::node_config::wasm("translator", "handler"),
        );
        let handler_init_sender =
            oak::io::entrypoint_node_create::<Node>("handler", &Label::public_untrusted(), "app")?;
        let handler_command_sender = oak::io::send_init(
            handler_init_sender,
            translator_sender_result
                .map(Either::Right)
                .unwrap_or(Either::Left(())),
            &Label::public_untrusted(),
        )?;
        oak::grpc::server::init_with_sender("[::]:8080", handler_command_sender)?;
        Ok(())
    }
}

struct Node {
    translator: Option<translator_common::TranslatorClient>,
}

impl oak::WithInit for Node {
    // Since `Option<T>` is not directly `Encodable` and `Decodable`, we emulate it via a
    // `Either<(), T>`, which is isomorphic to it.
    type Init = Either<(), Sender<grpc::Invocation>>;

    fn create(init: Self::Init) -> Self {
        Node {
            translator: init.right().map(translator_common::TranslatorClient),
        }
    }
}

oak::entrypoint_command_handler_init!(node => Node);
oak::impl_dispatcher!(impl Node : HelloWorldDispatcher);

impl Node {
    fn translate(&self, text: &str, from_lang: &str, to_lang: &str) -> Option<String> {
        let client = self.translator.as_ref()?;
        translator_common::translate(client, text, from_lang, to_lang)
    }
}

impl HelloWorld for Node {
    fn say_hello(&mut self, req: HelloRequest) -> grpc::Result<HelloResponse> {
        info!("Say hello to {}", req.greeting);
        let mut res = HelloResponse::default();
        res.reply = format!("HELLO {}!", req.greeting);
        Ok(res)
    }

    fn lots_of_replies(&mut self, req: HelloRequest, writer: grpc::ChannelResponseWriter) {
        info!("Say hello to {}", req.greeting);
        let mut res1 = HelloResponse::default();
        res1.reply = format!("HELLO {}!", req.greeting);
        writer
            .write(&res1, grpc::WriteMode::KeepOpen)
            .expect("Failed to write response");

        // Attempt to also generate a translated response.
        if let Some(salutation) = self.translate(&req.greeting, "en", "fr") {
            info!("Say bonjour to {}", salutation);
            let mut res = HelloResponse::default();
            res.reply = format!("BONJOUR {}!", salutation);
            writer
                .write(&res, grpc::WriteMode::KeepOpen)
                .expect("Failed to write translated response");
        }

        info!("Say hello again to {}", req.greeting);
        let mut res2 = HelloResponse::default();
        res2.reply = format!("HELLO AGAIN {}!", req.greeting);
        writer
            .write(&res2, grpc::WriteMode::Close)
            .expect("Failed to write final response");
    }

    fn lots_of_greetings(&mut self, reqs: Vec<HelloRequest>) -> grpc::Result<HelloResponse> {
        info!("Say hello");
        let mut msg = String::new();
        msg.push_str("Hello ");
        msg.push_str(&recipients(&reqs));
        let mut res = HelloResponse::default();
        res.reply = msg;
        Ok(res)
    }

    fn bidi_hello(&mut self, reqs: Vec<HelloRequest>, writer: grpc::ChannelResponseWriter) {
        info!("Say hello");
        let msg = recipients(&reqs);
        let mut res1 = HelloResponse::default();
        res1.reply = format!("HELLO {}!", msg);
        writer
            .write(&res1, grpc::WriteMode::KeepOpen)
            .expect("Failed to write response");
        let mut res2 = HelloResponse::default();
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
