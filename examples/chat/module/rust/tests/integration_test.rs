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
use chat_grpc::proto::{
    chat_client::ChatClient, CreateRoomRequest, DestroyRoomRequest, Message, SendMessageRequest,
    SubscribeRequest,
};
use futures::executor::block_on;
use log::info;
use serial_test::serial;
use std::sync::{Arc, Condvar, Mutex};
use tokio::sync::Semaphore;

const MODULE_WASM_FILE_NAME: &str = "chat.wasm";

#[tokio::test(core_threads = 2)]
#[serial]
async fn test_room_create() {
    let _ = env_logger::try_init();

    let runtime = oak_tests::run_single_module(MODULE_WASM_FILE_NAME, "grpc_oak_main")
        .expect("Unable to configure runtime with test wasm!");

    let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
    let mut client = ChatClient::with_interceptor(channel, interceptor);

    let req = CreateRoomRequest {
        room_id: b"dummy room id".to_vec(),
        admin_token: b"dummy admin token".to_vec(),
    };
    info!("Sending request: {:?}", req);
    let result = client.create_room(req).await;
    assert_matches!(result, Ok(_));

    // Fail to destroy a non-existent room.
    let req = DestroyRoomRequest {
        room_id: b"unknown room id".to_vec(),
        admin_token: b"dummy admin token".to_vec(),
    };
    info!("Sending request: {:?}", req);
    let result = client.destroy_room(req).await;
    assert_matches!(result, Err(_));

    // Succeed in destroying the room created above.
    let req = DestroyRoomRequest {
        room_id: b"dummy room id".to_vec(),
        admin_token: b"dummy admin token".to_vec(),
    };
    info!("Sending request: {:?}", req);
    let result = client.destroy_room(req.clone()).await;
    assert_matches!(result, Ok(_));

    // ...but fail to destroy it a second time.
    info!("Sending request: {:?}", req);
    let result = client.destroy_room(req).await;
    assert_matches!(result, Err(_));

    runtime.stop();
}

#[tokio::test(core_threads = 4)]
#[serial]
async fn test_chat() {
    let _ = env_logger::try_init();

    let runtime = oak_tests::run_single_module(MODULE_WASM_FILE_NAME, "grpc_oak_main")
        .expect("Unable to configure runtime with test wasm!");

    let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
    let mut client = ChatClient::with_interceptor(channel, interceptor);

    let room_id = b"test room";
    let req = CreateRoomRequest {
        room_id: room_id.to_vec(),
        admin_token: b"dummy admin token".to_vec(),
    };
    info!("Sending request: {:?}", req);
    let result = client.create_room(req).await;
    assert_matches!(result, Ok(_));

    let mut alice = Chatter::new(room_id, "Alice");
    let mut bob = Chatter::new(room_id, "Bob");

    let msgs = Arc::new(ChatLog::default());
    let msgs_ref = msgs.clone();
    let subscribed = Arc::new(Semaphore::new(0));
    let s = subscribed.clone();
    let r = room_id.to_vec();
    tokio::spawn(async move { subscribe(r, msgs_ref, s).await });
    subscribed.acquire().await.forget();

    alice.send("Hello");
    msgs.await_size(1);
    assert_eq!(vec!["Alice: Hello"], msgs.contents());

    bob.send("Hello there yourself");
    msgs.await_size(2);
    assert_eq!(
        vec!["Alice: Hello", "Bob: Hello there yourself"],
        msgs.contents()
    );

    // A new subscription only sees subsequent messages.
    let later_msgs = Arc::new(ChatLog::default());
    let later_msgs_ref = later_msgs.clone();
    let s = subscribed.clone();
    let r = room_id.to_vec();
    tokio::spawn(async move { subscribe(r, later_msgs_ref, s).await });
    subscribed.acquire().await.forget();

    alice.send("Hello again");
    msgs.await_size(3);
    assert_eq!(
        vec![
            "Alice: Hello",
            "Bob: Hello there yourself",
            "Alice: Hello again"
        ],
        msgs.contents()
    );
    later_msgs.await_size(1);
    assert_eq!(vec!["Alice: Hello again"], later_msgs.contents());

    runtime.stop();
}

// Thread-safe vector of messages.
#[derive(Default)]
struct ChatLog {
    messages: Mutex<Vec<String>>,
    cv: Condvar,
}

impl ChatLog {
    pub fn contents(&self) -> Vec<String> {
        let msgs = self.messages.lock().expect("lock poisoned");
        msgs.iter().cloned().collect()
    }

    pub fn push_message(&self, msg: &Message) {
        let mut msgs = self.messages.lock().expect("lock poisoned");
        msgs.push(format!("{}: {}", msg.user_handle, msg.text));
        self.cv.notify_all();
    }

    // Block until there are at least `count` messages available.
    pub fn await_size(&self, count: usize) {
        let mut msgs = self.messages.lock().expect("lock poisoned");
        while msgs.len() < count {
            msgs = self.cv.wait(msgs).unwrap();
        }
    }
}

struct Chatter {
    pub client: ChatClient<tonic::transport::Channel>,
    pub room_id: Vec<u8>,
    pub user_handle: String,
}

impl Chatter {
    pub fn new(room_id: &[u8], user_handle: &str) -> Chatter {
        info!(
            "creating new Chatter({}, {})",
            user_handle,
            base64::encode(room_id)
        );
        let (channel, interceptor) = block_on(oak_tests::channel_and_interceptor());
        let client = ChatClient::with_interceptor(channel, interceptor);
        Chatter {
            client,
            room_id: room_id.to_vec(),
            user_handle: user_handle.to_string(),
        }
    }

    pub fn send(&mut self, text: &str) {
        let req = SendMessageRequest {
            room_id: self.room_id.clone(),
            message: Some(Message {
                user_handle: self.user_handle.clone(),
                text: text.to_string(),
            }),
        };
        info!("Sending request: {:?}", req);
        let result = block_on(self.client.send_message(req));
        assert_matches!(result, Ok(_));
    }
}

async fn subscribe(room_id: Vec<u8>, msgs: Arc<ChatLog>, s: Arc<Semaphore>) {
    info!("Subscribe to messages in room {}", base64::encode(&room_id));

    let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
    let mut client = ChatClient::with_interceptor(channel, interceptor);
    let req = SubscribeRequest {
        room_id: room_id.clone(),
    };
    info!("Sending request: {:?}", req);
    let mut stream = client.subscribe(req).await.unwrap().into_inner();
    s.add_permits(1);

    while let Some(msg) = stream.message().await.unwrap() {
        info!("Received {:?}", msg);
        msgs.push_message(&msg);
    }

    info!(
        "Stream closed, ending subscription to room {}",
        base64::encode(&room_id)
    );
}
