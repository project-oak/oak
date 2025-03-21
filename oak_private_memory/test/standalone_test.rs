//
// Copyright 2025 The Project Oak Authors
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

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use anyhow::{Context, Result};
use futures::channel::mpsc;
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};
use oak_sdk_server_v1::OakApplicationContext;
use oak_sdk_standalone::Standalone;
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ProtocolEngine,
    Session,
};
use private_memory_server_lib::{
    app::{RequestUnpacking, ResponsePacking},
    app_config::ApplicationConfig,
};
use prost::Message;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_service_client::SealedMemoryServiceClient;
use sealed_memory_rust_proto::oak::private_memory::{
    sealed_memory_response, AddMemoryRequest, AddMemoryResponse, GetMemoriesRequest,
    GetMemoriesResponse, InvalidRequestResponse, KeySyncRequest, KeySyncResponse, Memory,
    SealedMemoryResponse,
};
use tokio::net::TcpListener;
use tonic::transport::Channel;

async fn start_server() -> Result<(
    SocketAddr,
    SocketAddr,
    tokio::task::JoinHandle<Result<()>>,
    tokio::task::JoinHandle<Result<()>>,
)> {
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await?;
    let addr = listener.local_addr()?;

    let db_addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let db_listener = TcpListener::bind(db_addr).await?;
    let db_addr = db_listener.local_addr()?;

    let application_config = ApplicationConfig { database_service_host: db_addr };

    let application_config_vec = serde_json::to_vec(&application_config)?;

    let standalone = Standalone::builder()
        .application_config(application_config_vec.clone())
        .build()
        .expect("failed to create Oak standalone elements");

    Ok((
        addr,
        db_addr,
        tokio::spawn(private_memory_server_lib::app_service::create(
            listener,
            OakApplicationContext::new(
                Box::new(standalone.encryption_key_handle()),
                standalone.endorsed_evidence(),
                Box::new(
                    private_memory_server_lib::app::SealedMemoryHandler::new(
                        &application_config_vec,
                    )
                    .await,
                ),
            ),
            Box::new(
                private_memory_server_lib::app::SealedMemoryHandler::new(&application_config_vec)
                    .await,
            ),
        )),
        tokio::spawn(private_memory_database_server_lib::service::create(db_listener)),
    ))
}

#[async_trait::async_trait]
trait ClientSessionHelper {
    fn encrypt_request(&mut self, request: &[u8]) -> anyhow::Result<SessionRequest>;
    fn decrypt_response(&mut self, session_response: &SessionResponse) -> anyhow::Result<Vec<u8>>;
    async fn init_session(
        &mut self,
        send_request: &mut mpsc::Sender<SessionRequest>,
        receive_response: &mut tonic::Streaming<SessionResponse>,
    ) -> anyhow::Result<()>;
}

#[async_trait::async_trait]
impl ClientSessionHelper for oak_session::ClientSession {
    fn encrypt_request(&mut self, request: &[u8]) -> anyhow::Result<SessionRequest> {
        self.write(PlaintextMessage { plaintext: request.to_vec() })
            .context("couldn't write message to encrypt")?;

        self.get_outgoing_message()
            .context("error getting encrypted request")?
            .ok_or_else(|| anyhow::anyhow!("no encrypted request"))
    }

    fn decrypt_response(&mut self, session_response: &SessionResponse) -> anyhow::Result<Vec<u8>> {
        self.put_incoming_message(session_response)
            .context("failed to put response for decryption")?;

        self.read()
            .context("error reading decrypted response")?
            .ok_or_else(|| anyhow::anyhow!("no encrypted response"))
            .map(|p| p.plaintext)
    }

    async fn init_session(
        &mut self,
        send_request: &mut mpsc::Sender<SessionRequest>,
        receive_response: &mut tonic::Streaming<SessionResponse>,
    ) -> Result<()> {
        while !self.is_open() {
            let init_request =
                self.get_outgoing_message().context("error getting init_message")?.ok_or_else(
                    || anyhow::anyhow!("no init message provided, but session not initialized"),
                )?;

            send_request.try_send(init_request).context("failed to send init request")?;

            if let Some(init_response) =
                receive_response.message().await.context("failed to receive response")?
            {
                self.put_incoming_message(&init_response)
                    .context("error putting init_response response")?;
            }
        }
        Ok(())
    }
}

fn send_plantext_request<T: RequestUnpacking>(
    sender: &mut mpsc::Sender<SessionRequest>,
    client_session: &mut oak_session::ClientSession,
    request: T,
) {
    let sealed_memory_request = request.into_request();
    let encrypted_request = client_session
        .encrypt_request(&sealed_memory_request.encode_to_vec())
        .expect("failed to encrypt message");
    sender.try_send(encrypted_request).expect("Could not send request to server");
}

async fn receive_plaintext_response<T: ResponsePacking>(
    receiver: &mut tonic::Streaming<SessionResponse>,
    client_session: &mut oak_session::ClientSession,
) -> T {
    let response =
        receiver.message().await.expect("error getting response").expect("didn't get any repsonse");

    let decrypted_response =
        client_session.decrypt_response(&response).expect("failed to decrypt response");

    T::from_response(
        SealedMemoryResponse::decode(decrypted_response.as_ref()).expect("Not a valid response"),
    )
    .expect("A different type of request is parsed!")
}

#[tokio::test]
async fn test_noise_handshake() {
    // Start server
    let (addr, _db_addr, _join_handle, _join_handle2) = start_server().await.unwrap();

    let url = format!("http://{addr}");

    println!("Connecting to test server on {}", url);

    let channel = Channel::from_shared(url)
        .context("couldn't create gRPC channel")
        .unwrap()
        .connect()
        .await
        .context("couldn't connect via gRPC channel")
        .unwrap();

    let mut client = SealedMemoryServiceClient::new(channel);

    let (mut tx, rx) = mpsc::channel(10);

    let mut response_stream =
        client.invoke(rx).await.expect("couldn't send stream request").into_inner();

    // We don't have a noise client impl yet, so we need to manage the session
    // manually.
    let mut client_session = oak_session::ClientSession::create(
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
    )
    .expect("could not create client session");

    client_session.init_session(&mut tx, &mut response_stream).await.expect("failed to handshake");

    let request =
        client_session.encrypt_request(b"standalone user").expect("failed to encrypt message");

    tx.try_send(request).expect("Could not send request to server");

    let response = response_stream
        .message()
        .await
        .expect("error getting response")
        .expect("didn't get any repsonse");

    let decrypted_response =
        client_session.decrypt_response(&response).expect("failed to decrypt response");

    let expected_response = SealedMemoryResponse {
        response: Some(sealed_memory_response::Response::InvalidRequestResponse(
            InvalidRequestResponse { error_message: "Invalid json or binary proto format".into() },
        )),
    };
    assert_eq!(decrypted_response, expected_response.encode_to_vec());
}

#[tokio::test]
async fn test_noise_add_get_memory() {
    // Start server
    let (addr, _db_addr, _join_handle, _join_handle2) = start_server().await.unwrap();

    let url = format!("http://{addr}");

    println!("Connecting to test server on {}", url);

    let channel = Channel::from_shared(url)
        .context("couldn't create gRPC channel")
        .unwrap()
        .connect()
        .await
        .context("couldn't connect via gRPC channel")
        .unwrap();

    let mut client = SealedMemoryServiceClient::new(channel);

    let (mut tx, rx) = mpsc::channel(10);

    let mut response_stream =
        client.invoke(rx).await.expect("couldn't send stream request").into_inner();

    // We don't have a noise client impl yet, so we need to manage the session
    // manually.
    let mut client_session = oak_session::ClientSession::create(
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
    )
    .expect("could not create client session");

    client_session.init_session(&mut tx, &mut response_stream).await.expect("failed to handshake");

    // Key sync
    let key_sync_request = KeySyncRequest { data_encryption_key: b"key".to_vec(), uid: 234 };
    send_plantext_request(&mut tx, &mut client_session, key_sync_request);

    let _key_sync_response: KeySyncResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    let request = AddMemoryRequest {
        memory: Some(Memory {
            id: "".to_string(),
            content: "this is a test".as_bytes().to_vec(),
            tags: vec!["tag".to_string()],
        }),
    };
    send_plantext_request(&mut tx, &mut client_session, request);

    let add_memory_response: AddMemoryResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    assert_eq!(add_memory_response.id, "0");

    let request = GetMemoriesRequest { tag: "tag".to_string() };
    send_plantext_request(&mut tx, &mut client_session, request);

    let get_memories_response: GetMemoriesResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    assert_eq!(get_memories_response.memories.len(), 1);
}
