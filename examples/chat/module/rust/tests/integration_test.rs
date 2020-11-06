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

    let runtime = oak_tests::run_single_module(MODULE_WASM_FILE_NAME, "main")
        .expect("could not configure runtime with test Wasm file");

    let room_0_key_pair = oak_sign::KeyPair::generate().expect("could not generate room key pair");
    let room_1_key_pair = oak_sign::KeyPair::generate().expect("could not generate room key pair");

    let mut alice = Chatter::new(&room_0_key_pair, "Alice").await;
    let mut alice_stream = alice.subscribe().await;

    let mut bob = Chatter::new(&room_0_key_pair, "Bob").await;
    let mut bob_stream = bob.subscribe().await;

    // Eve joins a different room, so she should not receive any messages between Alice and Bob.
    // Because of the asynchronous nature of the interaction, it is not possible to conclusively
    // determine whether Eve did not receive a particular message, therefore below we just await
    // for a short amount of time (via `tokio::time::timeout`) before assuming that she didn't.
    let mut eve = Chatter::new(&room_1_key_pair, "Eve").await;
    let mut eve_stream = eve.subscribe().await;

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
        // TODO(#1357): Verify that Eve indeed does not receive the message.
        // assert_matches!(
        //     tokio::time::timeout(Duration::from_millis(100), eve_stream.message()).await,
        //     Err(_)
        // );
        assert_eq!(
            expected_message,
            eve_stream.message().await.unwrap().unwrap()
        );
    }

    let mut charlie = Chatter::new(&room_0_key_pair, "Charlie").await;
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
        // TODO(#1357): Verify that Eve indeed does not receive the message.
        // assert_matches!(
        //     tokio::time::timeout(Duration::from_millis(100), eve_stream.message()).await,
        //     Err(_)
        // );
        assert_eq!(
            expected_message,
            eve_stream.message().await.unwrap().unwrap()
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
        // TODO(#1357): Verify that Eve indeed does not receive the message.
        // assert_matches!(
        //     tokio::time::timeout(Duration::from_millis(100), eve_stream.message()).await,
        //     Err(_)
        // );
        assert_eq!(
            expected_message,
            eve_stream.message().await.unwrap().unwrap()
        );
    }

    runtime.stop();
}

struct Chatter<'a> {
    pub client: ChatClient<tonic::transport::Channel>,
    pub room_key_pair: &'a oak_sign::KeyPair,
    pub user_handle: String,
}

impl<'a> Chatter<'a> {
    pub async fn new(
        room_key_pair: &'a oak_sign::KeyPair,
        user_handle: &'static str,
    ) -> Chatter<'a> {
        info!(
            "creating new Chatter({}, {})",
            user_handle,
            base64::encode(&room_key_pair.pkcs8_public_key())
        );
        let (channel, interceptor) = oak_tests::public_channel_and_interceptor().await;
        // TODO(#1357): Use key pair to authenticate this client and label requests.
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
