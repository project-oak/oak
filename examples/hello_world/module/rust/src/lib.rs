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
    pub mod oak {
        pub use oak::proto::oak::invocation;
        pub use oak_services::proto::oak::log;
        pub mod examples {
            pub mod hello_world {
                include!(concat!(env!("OUT_DIR"), "/oak.examples.hello_world.rs"));
            }
        }
    }
}

use log::info;
use oak::grpc;
use oak_abi::{label::Label, proto::oak::application::ConfigMap};
use oak_services::proto::oak::log::LogInit;
use proto::oak::examples::hello_world::{
    HelloRequest, HelloResponse, HelloWorld, HelloWorldDispatcher, Init,
};

#[derive(Default)]
struct Main;

oak::entrypoint_command_handler!(oak_main => Main);

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: Self::Command) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        oak::logger::init(log_sender.clone(), log::Level::Debug)?;
        let translator_sender_option =
            oak::io::entrypoint_node_create::<translator_common::TranslatorEntrypoint, _, _>(
                "translator",
                &Label::public_untrusted(),
                "translator",
                LogInit {
                    log_sender: Some(log_sender.clone()),
                },
            )
            .ok();
        if translator_sender_option == None {
            log::warn!("could not create translator node");
        }
        let handler_sender = oak::io::entrypoint_node_create::<Handler, _, _>(
            "handler",
            &Label::public_untrusted(),
            "app",
            Init {
                log_sender: Some(log_sender),
                translator_sender: translator_sender_option,
            },
        )?;
        oak::grpc::server::init_with_sender("[::]:8080", handler_sender)?;
        Ok(())
    }
}

struct Handler {
    translator: Option<translator_common::TranslatorClient>,
}

impl oak::WithInit for Handler {
    type Init = Init;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        Self {
            translator: init
                .translator_sender
                .map(translator_common::TranslatorClient),
        }
    }
}

oak::entrypoint_command_handler_init!(handler => Handler);
oak::impl_dispatcher!(impl Handler : HelloWorldDispatcher);

impl Handler {
    fn translate(&self, text: &str, from_lang: &str, to_lang: &str) -> Option<String> {
        let client = self.translator.as_ref()?;
        translator_common::translate(client, text, from_lang, to_lang)
    }
}

impl HelloWorld for Handler {
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
