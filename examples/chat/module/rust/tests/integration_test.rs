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
use chat_grpc::proto::{chat_client::ChatClient, CreateRoomRequest, DestroyRoomRequest};
use log::info;

const MODULE_WASM_FILE_NAME: &str = "chat.wasm";

#[tokio::test(core_threads = 2)]
async fn test_room_create() {
    env_logger::init();

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
