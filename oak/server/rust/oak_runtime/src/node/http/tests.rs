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

use super::*;
use maplit::hashmap;
use oak_abi::{label::Label, proto::oak::application::ApplicationConfiguration};
use std::{collections::HashMap, thread};

#[tokio::test]
#[ignore]
// Might be unstable when running from `run-ci`. So it is ignored for now.
async fn test_low_level_server_node() {
    let configuration = ApplicationConfiguration {
        wasm_modules: hashmap! {},
        initial_node_configuration: None,
    };
    info!("Create runtime for test");
    let runtime = crate::runtime::RuntimeProxy::create_runtime(
        &configuration,
        &crate::GrpcConfiguration::default(),
    );

    let (init_receiver, invocation_receiver) = create_communication_channel(&runtime);

    // Create http server node
    let server_node = Box::new(
        HttpServerNode::new(
            "test-node",
            HttpServerConfiguration {
                address: "[::]:2525".to_string(),
            },
        )
        .expect("Could not create server node"),
    );

    // Start the server node
    let (notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();
    let runtime_proxy = runtime.clone();
    // TODO(#1186): Use tokio instead of spawning a thread.
    let server_node_thread =
        std::thread::spawn(move || server_node.run(runtime_proxy, init_receiver, notify_receiver));

    // Simulate an Oak node that responds with 200 (OK) to every request it receives
    // TODO(#1186): Use tokio instead of spawning a thread.
    let runtime_proxy = runtime.clone();
    let oak_node_simulator_thread = thread::Builder::new()
        .name("Oak node simulator".to_string())
        .spawn(move || {
            oak_node_simulator(&runtime_proxy, invocation_receiver);
        })
        .expect("Error when spawning the thread.");

    // Send a request, and await on the response
    let resp = send_request().await;

    assert_eq!(resp.status(), http::status::StatusCode::OK.as_u16());

    notify_sender.send(()).unwrap_or_else(|()| {
        debug!("Test node already dropped `notify_receiver`.");
    });
    let _ = server_node_thread.join();
    let _ = oak_node_simulator_thread.join();

    // Clean up - stop the runtime ans any servers it is running
    runtime.runtime.stop();
}

fn create_communication_channel(runtime: &RuntimeProxy) -> (oak_abi::Handle, oak_abi::Handle) {
    // create channel: one end to server_node::run; the other to the Oak node.
    let (init_sender, init_receiver) = runtime
        .channel_create(&Label::public_untrusted())
        .expect("Could not create channel");

    // At the start the HTTP server pseudo-Node expects to receive an invocation channel, with
    // exactly one handle in it.
    //
    // Create a channel for receiving invocations to pass to the HTTP server pseudo-Node.
    let (invocation_sender, invocation_receiver) = runtime
        .channel_create(&Label::public_untrusted())
        .expect("Could not create channel");
    let message = crate::NodeMessage {
        data: vec![],
        handles: vec![invocation_sender],
    };

    let _ = runtime
        .channel_write(init_sender, message)
        .map_err(|err| panic!("Could not write to the `init_sender` channel: {}", err));
    let _ = runtime
        .channel_close(init_sender)
        .map_err(|err| panic!("Could not close the `init_sender` channel: {}.", err));

    (init_receiver, invocation_receiver)
}

fn oak_node_simulator(runtime: &RuntimeProxy, invocation_receiver: oak_abi::Handle) {
    // Get invocation message that contains the response_writer handle.
    let read_status = runtime
        .wait_on_channels(&[invocation_receiver])
        .expect("Error while waiting on invocation_receiver");
    if read_status[0] == ChannelReadStatus::ReadReady {
        if let Ok(Some(msg)) = runtime.channel_read(invocation_receiver) {
            // Prepare the response
            let resp = HttpResponse {
                body: vec![],
                status: http::status::StatusCode::OK.as_u16() as i32,
                headers: HashMap::new(),
            };
            let mut message = crate::NodeMessage {
                data: vec![],
                handles: vec![],
            };
            let _ = resp.encode(&mut message.data);

            // Send the response over the response_writer channel
            let response_writer_handle = msg.handles[1];
            let _ = runtime.channel_write(response_writer_handle, message);
        }
    } else {
        panic!("Error while waiting for message on invocation_receiver");
    }
}

async fn send_request() -> reqwest::Response {
    // Send a request, and wait for the response
    let label = oak_abi::label::Label::public_untrusted();
    let mut label_bytes = vec![];
    let _ = label.encode(&mut label_bytes);

    reqwest::Client::new()
        .get("http://localhost:2525")
        .header(oak_abi::OAK_LABEL_HTTP_KEY, label_bytes)
        .send()
        .await
        .expect("Error while awaiting response")
}
