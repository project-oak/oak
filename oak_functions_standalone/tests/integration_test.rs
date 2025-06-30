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

use oak_functions_service::wasm::wasmtime::WasmtimeHandler;
use oak_functions_standalone::{serve, OakFunctionsSessionArgs};
use oak_grpc::oak::functions::standalone::oak_functions_session_client::OakFunctionsSessionClient;
use oak_proto_rust::oak::{
    functions::{
        standalone::{OakSessionRequest, OakSessionResponse},
        InitializeRequest,
    },
    session::v1::{
        session_request::Request, session_response::Response, EncryptedMessage, SessionRequest,
        SessionResponse,
    },
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

    let ciphertext_message = "Hello World".as_bytes().to_vec();

    let iterator = tokio_stream::iter(vec![OakSessionRequest {
        request: Some(SessionRequest {
            request: Some(Request::EncryptedMessage(EncryptedMessage {
                ciphertext: ciphertext_message.clone(),
                associated_data: None,
                nonce: None,
            })),
        }),
    }]);

    let response_stream = oak_functions_session_client.oak_session(iterator).await.unwrap();

    let resp_stream: tonic::Streaming<OakSessionResponse> = response_stream.into_inner();

    let response_vector: Vec<OakSessionResponse> =
        resp_stream.map(|response| response.unwrap()).collect().await;

    assert_eq!(response_vector.len(), 1);
    assert_eq!(
        response_vector[0],
        OakSessionResponse {
            response: Some(SessionResponse {
                response: Some(Response::EncryptedMessage(EncryptedMessage {
                    ciphertext: ciphertext_message,
                    associated_data: None,
                    nonce: None,
                })),
            })
        }
    );

    server_handle.abort();
    let _ = server_handle.await;
}
