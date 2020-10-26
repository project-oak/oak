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

use assert_matches::assert_matches;
use chat_grpc::proto::{chat_client::ChatClient, Message, SendMessageRequest, SubscribeRequest};
use log::info;
use serial_test::serial;

const MODULE_WASM_FILE_NAME: &str = "chat.wasm";

#[tokio::test(core_threads = 4)]
#[serial]
async fn test_chat() {
    let _ = env_logger::builder().is_test(true).try_init();

    let runtime = oak_tests::run_single_module(MODULE_WASM_FILE_NAME, "grpc_oak_main")
        .expect("Unable to configure runtime with test wasm!");

    let room_key_pair = oak_sign::KeyBundle::generate().expect("could not generate room key pair");

    let mut alice = Chatter::new(&room_key_pair, "Alice").await;
    let mut alice_stream = alice.subscribe().await;

    let mut bob = Chatter::new(&room_key_pair, "Bob").await;
    let mut bob_stream = bob.subscribe().await;

    alice.send("Hello").await;
    {
        let expected_message = Message {
            user_handle: "Alice".to_string(),
            text: "Hello".to_string(),
        };
        assert_eq!(
            expected_message,
            alice_stream.message().await.unwrap().unwrap()
        );
        assert_eq!(
            expected_message,
            bob_stream.message().await.unwrap().unwrap()
        );
    }

    let mut charlie = Chatter::new(&room_key_pair, "Charlie").await;
    // Do not subscribe Charlie yet.

    charlie.send("Hello there yourself").await;
    {
        let expected_message = Message {
            user_handle: "Charlie".to_string(),
            text: "Hello there yourself".to_string(),
        };
        assert_eq!(
            expected_message,
            alice_stream.message().await.unwrap().unwrap()
        );
        assert_eq!(
            expected_message,
            bob_stream.message().await.unwrap().unwrap()
        );
    }

    // Subscribe Charlie after a few messages have been exchanged, and check it receives any new
    // messages.
    let mut charlie_stream = charlie.subscribe().await;
    bob.send("Goodbye").await;
    {
        let expected_message = Message {
            user_handle: "Bob".to_string(),
            text: "Goodbye".to_string(),
        };
        assert_eq!(
            expected_message,
            alice_stream.message().await.unwrap().unwrap()
        );
        assert_eq!(
            expected_message,
            bob_stream.message().await.unwrap().unwrap()
        );
        assert_eq!(
            expected_message,
            charlie_stream.message().await.unwrap().unwrap()
        );
    }

    runtime.stop();
}

struct Chatter<'a> {
    pub client: ChatClient<tonic::transport::Channel>,
    pub room_key_pair: &'a oak_sign::KeyBundle,
    pub user_handle: String,
}

impl<'a> Chatter<'a> {
    pub async fn new(
        room_key_pair: &'a oak_sign::KeyBundle,
        user_handle: &'static str,
    ) -> Chatter<'a> {
        info!(
            "creating new Chatter({}, {})",
            user_handle,
            base64::encode(&room_key_pair.public_key())
        );
        let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
        let client = ChatClient::with_interceptor(channel, interceptor);
        Chatter {
            client,
            room_key_pair,
            user_handle: user_handle.to_string(),
        }
    }

    pub async fn send(&mut self, text: &str) {
        let req = SendMessageRequest {
            message: Some(Message {
                user_handle: self.user_handle.clone(),
                text: text.to_string(),
            }),
        };
        info!("Sending request: {:?}", req);
        let result = self.client.send_message(req).await;
        assert_matches!(result, Ok(_));
    }

    pub async fn subscribe(&mut self) -> tonic::Streaming<Message> {
        let req = SubscribeRequest {};
        info!("Sending request: {:?}", req);
        self.client.subscribe(req).await.unwrap().into_inner()
    }
}
