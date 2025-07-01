//
// Copyright 2023 The Project Oak Authors
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

use std::{
    fs,
    net::{IpAddr, Ipv4Addr, SocketAddr},
    time::Duration,
};

use futures::channel::mpsc;
use oak_functions_service::wasm::wasmtime::WasmtimeHandler;
use oak_functions_standalone::{serve, OakFunctionsSessionArgs};
use oak_grpc::oak::functions::standalone::oak_functions_session_client::OakFunctionsSessionClient;
use oak_proto_rust::oak::functions::{
    standalone::{OakSessionRequest, OakSessionResponse},
    InitializeRequest,
};
use oak_session::{
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
    Session,
};
use tokio::net::TcpListener;
use tokio_stream::{wrappers::TcpListenerStream, StreamExt};
use tonic::{codec::CompressionEncoding, transport::Endpoint};

#[tokio::test]
async fn test_echo() {
    // To be used to load the Wasm module.
    let wasm_path = "oak_functions/examples/echo/echo.wasm";

    let (addr, stream) = {
        let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
        let listener = TcpListener::bind(addr).await.unwrap();
        let addr = listener.local_addr().unwrap();
        (addr, Box::new(TcpListenerStream::new(listener)))
    };

    let oak_functions_session_args = OakFunctionsSessionArgs {
        wasm_initialization: InitializeRequest {
            constant_response_size: 100, // This value is ultimately ignored.
            wasm_module: fs::read(wasm_path).expect("failed to read wasm module"),
        },
    };

    let server_handle = tokio::spawn(serve::<WasmtimeHandler>(
        stream,
        Default::default(),
        oak_functions_session_args,
    ));

    let mut oak_functions_session_client: OakFunctionsSessionClient<
        tonic::transport::channel::Channel,
    > = {
        let channel = Endpoint::from_shared(format!("http://{addr}"))
            .expect("couldn't form channel")
            .connect_timeout(Duration::from_secs(120))
            .connect()
            .await
            .expect("couldn't connect to trusted app");
        OakFunctionsSessionClient::new(channel).send_compressed(CompressionEncoding::Gzip)
    };

    let (mut tx, rx) = mpsc::channel(10);

    let response_stream = oak_functions_session_client.oak_session(rx).await.unwrap();

    let mut resp_stream: tonic::Streaming<OakSessionResponse> = response_stream.into_inner();

    let mut client_session = oak_session::ClientSession::create(
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
    )
    .expect("could not create client session");

    // Initialize encrypted channel.
    while !client_session.is_open() {
        let session_request =
            client_session.next_init_message().expect("expected client init message");
        let oak_session_request = OakSessionRequest { request: Some(session_request) };
        tx.try_send(oak_session_request).expect("failed to send to server");
        if !client_session.is_open() {
            let oak_session_response = resp_stream
                .message()
                .await
                .expect("expected a response")
                .expect("response was failure");
            client_session
                .handle_init_message(oak_session_response.response.expect("no session response"))
                .expect("failed to handle init response");
            println!("Client handshake is done");
        }
    }

    let test_message = "Hello World";

    let encrypted_request = client_session
        .encrypt(test_message.as_bytes().to_vec())
        .expect("failed to encrypt message");
    let oak_session_request = OakSessionRequest { request: Some(encrypted_request) };

    // Send our request and close the channel since we have no more messages to
    // send.
    tx.try_send(oak_session_request).expect("failed to send message");
    tx.close_channel();

    let response_vector: Vec<String> = resp_stream
        .map(|oak_session_response| {
            let response_bytes = client_session.decrypt(
                oak_session_response
                    .expect("empty response")
                    .response
                    .expect("empty session response"),
            );
            println!("We received a response");
            String::from_utf8(response_bytes.expect("unable to decrypt response"))
                .expect("unable to convert bytes to string")
        })
        .collect()
        .await;

    assert_eq!(response_vector.len(), 1);
    assert_eq!(response_vector[0], test_message);

    server_handle.abort();
    let _ = server_handle.await;
}
