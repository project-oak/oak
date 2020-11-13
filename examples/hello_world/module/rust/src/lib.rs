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
use futures::prelude::*;
use log::info;
use oak::{
    grpc,
    io::{Receiver, ReceiverExt},
};
use oak_abi::{label::Label, proto::oak::application::ConfigMap};
use oak_async::ChannelReadStream;
use oak_io::{InitWrapper, Sender};
use proto::{asynchronous::HelloWorld as HelloWorldAsync, HelloRequest, HelloResponse};

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
        let handler_init_sender = oak::io::node_create::<InitWrapper<Init, grpc::Invocation>>(
            "handler",
            &Label::public_untrusted(),
            &oak::node_config::wasm("app", "async_node"),
        )?;
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

struct Translator {
    client: Option<translator_common::TranslatorClient>,
}

impl Translator {
    pub fn translate(&self, text: &str, from_lang: &str, to_lang: &str) -> Option<String> {
        let client = self.client.as_ref()?;
        translator_common::translate(client, text, from_lang, to_lang)
    }
}

// The Init message received by `async_node`
// Since `Option<T>` is not directly `Encodable` and `Decodable`, we emulate it via a
// `Either<(), T>`, which is isomorphic to it.
type Init = Either<(), Sender<grpc::Invocation>>;

oak::entrypoint!(async_node <InitWrapper<Init, grpc::Invocation>> => async_node_entrypoint);
fn async_node_entrypoint(receiver: Receiver<InitWrapper<Init, grpc::Invocation>>) {
    let InitWrapper {
        init,
        command_receiver,
    } = receiver.receive().expect("Did not receive init message");
    let translator = Translator {
        client: init.right().map(translator_common::TranslatorClient),
    };
    oak_async::run_command_loop(command_receiver, |invocations| {
        hello_handler(translator, invocations)
    });
}

async fn hello_handler(translator: Translator, invocations: ChannelReadStream<grpc::Invocation>) {
    let translator = &translator;

    invocations
        .and_then(HelloWorldAsync::from_invocation)
        .try_for_each(|command| async {
            match command {
                HelloWorldAsync::SayHello(request, response_writer) => {
                    info!("Say hello to {}", request.greeting);
                    let mut res = HelloResponse::default();
                    res.reply = format!("HELLO {}!", request.greeting);
                    response_writer.send(&res)
                }
                HelloWorldAsync::LotsOfReplies(request, response_writer) => {
                    info!("Say hello to {}", request.greeting);
                    let mut res1 = HelloResponse::default();
                    res1.reply = format!("HELLO {}!", request.greeting);
                    response_writer
                        .send(&res1)
                        .expect("Failed to write response");

                    // Attempt to also generate a translated response.
                    if let Some(salutation) = translator.translate(&request.greeting, "en", "fr") {
                        info!("Say bonjour to {}", salutation);
                        let mut res = HelloResponse::default();
                        res.reply = format!("BONJOUR {}!", salutation);
                        response_writer
                            .send(&res)
                            .expect("Failed to write translated response");
                    }

                    info!("Say hello again to {}", request.greeting);
                    let mut res2 = HelloResponse::default();
                    res2.reply = format!("HELLO AGAIN {}!", request.greeting);
                    response_writer
                        .send(&res2)
                        .expect("Failed to write final response");
                    // response_writer is automatically closed when it is `Drop`ed
                    Ok(())
                }
                HelloWorldAsync::LotsOfGreetings(requests, response_writer) => {
                    info!("Say hello");
                    let mut res = HelloResponse::default();
                    res.reply = async_recipients(requests).await?;
                    response_writer.send(&res)
                }
                HelloWorldAsync::BidiHello(requests, response_writer) => {
                    info!("Say hello");
                    let msg = async_recipients(requests).await?;
                    let mut res1 = HelloResponse::default();
                    res1.reply = format!("HELLO {}!", msg);
                    response_writer
                        .send(&res1)
                        .expect("Failed to write response");
                    let mut res2 = HelloResponse::default();
                    res2.reply = format!("BONJOUR {}!", msg);
                    response_writer
                        .send(&res2)
                        .expect("Failed to write final response");
                    Ok(())
                }
            }
        })
        .await
        .expect("Error handling request");
}

async fn async_recipients(
    mut requests: oak_async::grpc::GrpcRequestStream<HelloRequest>,
) -> Result<String, oak::OakError> {
    let first_request = requests.try_next().await?.expect("Nobody to greet");
    let msg = format!("Hello, {}", &first_request.greeting);
    requests
        .try_fold(msg, |mut msg, req| async move {
            msg.push_str(", ");
            msg.push_str(&req.greeting);
            Ok(msg)
        })
        .await
}
