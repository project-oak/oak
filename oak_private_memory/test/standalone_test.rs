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
    boot_strap_response, key_sync_response, sealed_memory_response, AddMemoryRequest,
    AddMemoryResponse, BootStrapRequest, BootStrapResponse, Embedding, GetMemoriesRequest,
    GetMemoriesResponse, GetMemoryByIdRequest, GetMemoryByIdResponse, InvalidRequestResponse,
    KeyDerivationInfo, KeySyncRequest, KeySyncResponse, Memory, ResetMemoryRequest,
    ResetMemoryResponse, SealedMemoryResponse, SearchMemoryRequest, SearchMemoryResponse,
};
use tokio::net::TcpListener;
use tonic::transport::Channel;

static TEST_EK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";
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
            private_memory_server_lib::app::SealedMemoryHandler::new(&application_config_vec).await,
        )),
        tokio::spawn(private_memory_test_database_server_lib::service::create(db_listener)),
    ))
}

#[async_trait::async_trait]
trait ClientSessionHelper {
    fn encrypt_request(&mut self, request: &[u8]) -> anyhow::Result<SessionRequest>;
    fn decrypt_response(&mut self, session_response: SessionResponse) -> anyhow::Result<Vec<u8>>;
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

    fn decrypt_response(&mut self, session_response: SessionResponse) -> anyhow::Result<Vec<u8>> {
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
                self.put_incoming_message(init_response)
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
    send_plantext_request_with_id(sender, client_session, request, 0)
}

fn send_plantext_request_with_id<T: RequestUnpacking>(
    sender: &mut mpsc::Sender<SessionRequest>,
    client_session: &mut oak_session::ClientSession,
    request: T,
    request_id: i32,
) {
    let mut sealed_memory_request = request.into_request();
    sealed_memory_request.request_id = request_id;
    let encrypted_request = client_session
        .encrypt_request(&sealed_memory_request.encode_to_vec())
        .expect("failed to encrypt message");
    sender.try_send(encrypted_request).expect("Could not send request to server");
}

fn send_plantext_request_as_json<T: RequestUnpacking>(
    sender: &mut mpsc::Sender<SessionRequest>,
    client_session: &mut oak_session::ClientSession,
    request: T,
) {
    let sealed_memory_request = request.into_request();
    let encrypted_request = client_session
        .encrypt_request(serde_json::to_vec(&sealed_memory_request).unwrap().as_ref())
        .expect("failed to encrypt message");
    sender.try_send(encrypted_request).expect("Could not send request to server");
}

async fn receive_plaintext_response_as_json<T: ResponsePacking>(
    receiver: &mut tonic::Streaming<SessionResponse>,
    client_session: &mut oak_session::ClientSession,
) -> T {
    let response =
        receiver.message().await.expect("error getting response").expect("didn't get any repsonse");

    let decrypted_response =
        client_session.decrypt_response(response).expect("failed to decrypt response");

    T::from_response(
        serde_json::from_slice::<SealedMemoryResponse>(&decrypted_response)
            .expect("Not a valid response"),
    )
    .expect("A different type of request is parsed!")
}

async fn receive_plaintext_response<T: ResponsePacking>(
    receiver: &mut tonic::Streaming<SessionResponse>,
    client_session: &mut oak_session::ClientSession,
) -> T {
    receive_plaintext_response_with_id(receiver, client_session).await.0
}

async fn receive_plaintext_response_with_id<T: ResponsePacking>(
    receiver: &mut tonic::Streaming<SessionResponse>,
    client_session: &mut oak_session::ClientSession,
) -> (T, i32) {
    let response =
        receiver.message().await.expect("error getting response").expect("didn't get any repsonse");

    let decrypted_response =
        client_session.decrypt_response(response).expect("failed to decrypt response");
    let sealed_memory_response =
        SealedMemoryResponse::decode(decrypted_response.as_ref()).expect("Not a valid response");
    let request_id = sealed_memory_response.request_id;

    (
        T::from_response(sealed_memory_response).expect("A different type of request is parsed!"),
        request_id,
    )
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
        client_session.decrypt_response(response).expect("failed to decrypt response");

    let expected_response = SealedMemoryResponse {
        response: Some(sealed_memory_response::Response::InvalidRequestResponse(
            InvalidRequestResponse { error_message: "Invalid json or binary proto format".into() },
        )),
        request_id: 0,
    };
    assert_eq!(decrypted_response, expected_response.encode_to_vec());
}

#[tokio::test]
async fn test_noise_add_get_reset_memory() {
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

    let pm_uid = 234.to_string();
    let boot_strap_request = BootStrapRequest {
        key_encryption_key: TEST_EK.to_vec(),
        pm_uid: pm_uid.clone(),
        boot_strap_info: Some(KeyDerivationInfo::default()),
    };
    send_plantext_request(&mut tx, &mut client_session, boot_strap_request);
    let boot_strap_response: BootStrapResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    assert_eq!(boot_strap_response.status, boot_strap_response::Status::Success as i32);
    // Key sync
    let request_id = 0xeadbeef;
    let key_sync_request =
        KeySyncRequest { key_encryption_key: TEST_EK.to_vec(), pm_uid: pm_uid.clone() };
    send_plantext_request_with_id(&mut tx, &mut client_session, key_sync_request, request_id);

    let (key_sync_response, return_id): (KeySyncResponse, i32) =
        receive_plaintext_response_with_id(&mut response_stream, &mut client_session).await;
    assert_eq!(request_id, return_id);
    assert_eq!(key_sync_response.status, key_sync_response::Status::Success as i32);

    let request = AddMemoryRequest {
        memory: Some(Memory {
            id: "".to_string(),
            content: "this is a test".as_bytes().to_vec(),
            tags: vec!["tag".to_string()],
            ..Default::default()
        }),
    };
    send_plantext_request(&mut tx, &mut client_session, request);

    let add_memory_response: AddMemoryResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    let request = GetMemoriesRequest { tag: "tag".to_string() };
    send_plantext_request(&mut tx, &mut client_session, request);

    let get_memories_response: GetMemoriesResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    assert_eq!(get_memories_response.memories.len(), 1);

    let request = GetMemoryByIdRequest { id: add_memory_response.id };
    send_plantext_request(&mut tx, &mut client_session, request);

    let get_memory_by_id_response: GetMemoryByIdResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    assert!(get_memory_by_id_response.memory.is_some());
    assert_eq!(
        get_memories_response.memories[0].encode_to_vec(),
        get_memory_by_id_response.memory.unwrap().encode_to_vec()
    );

    let request = ResetMemoryRequest::default();
    send_plantext_request(&mut tx, &mut client_session, request);

    let reset_memory_response: ResetMemoryResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    assert!(reset_memory_response.success);

    let request = GetMemoriesRequest { tag: "tag".to_string() };
    send_plantext_request(&mut tx, &mut client_session, request);

    let get_memories_response: GetMemoriesResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    assert_eq!(get_memories_response.memories.len(), 0);
}

#[tokio::test]
async fn test_noise_add_get_reset_memory_as_json() {
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

    let pm_uid = 234.to_string();
    let boot_strap_request = BootStrapRequest {
        key_encryption_key: TEST_EK.to_vec(),
        pm_uid: pm_uid.clone(),
        boot_strap_info: Some(KeyDerivationInfo::default()),
    };
    send_plantext_request_as_json(&mut tx, &mut client_session, boot_strap_request);
    let boot_strap_response: BootStrapResponse =
        receive_plaintext_response_as_json(&mut response_stream, &mut client_session).await;

    assert_eq!(boot_strap_response.status, boot_strap_response::Status::Success as i32);

    // Key sync
    let key_sync_request =
        KeySyncRequest { key_encryption_key: TEST_EK.to_vec(), pm_uid: pm_uid.clone() };
    send_plantext_request_as_json(&mut tx, &mut client_session, key_sync_request);

    let _key_sync_response: KeySyncResponse =
        receive_plaintext_response_as_json(&mut response_stream, &mut client_session).await;

    let request = AddMemoryRequest {
        memory: Some(Memory {
            id: "".to_string(),
            content: "this is a test".as_bytes().to_vec(),
            tags: vec!["tag".to_string()],
            ..Default::default()
        }),
    };
    send_plantext_request_as_json(&mut tx, &mut client_session, request);

    let add_memory_response: AddMemoryResponse =
        receive_plaintext_response_as_json(&mut response_stream, &mut client_session).await;

    let request = GetMemoriesRequest { tag: "tag".to_string() };
    send_plantext_request_as_json(&mut tx, &mut client_session, request);

    let get_memories_response: GetMemoriesResponse =
        receive_plaintext_response_as_json(&mut response_stream, &mut client_session).await;

    assert_eq!(get_memories_response.memories.len(), 1);

    let request = GetMemoryByIdRequest { id: add_memory_response.id };
    send_plantext_request_as_json(&mut tx, &mut client_session, request);

    let get_memory_by_id_response: GetMemoryByIdResponse =
        receive_plaintext_response_as_json(&mut response_stream, &mut client_session).await;

    assert!(get_memory_by_id_response.memory.is_some());
    assert_eq!(
        get_memories_response.memories[0].encode_to_vec(),
        get_memory_by_id_response.memory.unwrap().encode_to_vec()
    );

    let request = ResetMemoryRequest::default();
    send_plantext_request_as_json(&mut tx, &mut client_session, request);

    let reset_memory_response: ResetMemoryResponse =
        receive_plaintext_response_as_json(&mut response_stream, &mut client_session).await;

    assert!(reset_memory_response.success);

    let request = GetMemoriesRequest { tag: "tag".to_string() };
    send_plantext_request_as_json(&mut tx, &mut client_session, request);

    let get_memories_response: GetMemoriesResponse =
        receive_plaintext_response_as_json(&mut response_stream, &mut client_session).await;
    assert_eq!(get_memories_response.memories.len(), 0);
}

#[test]
fn proto_serialization_test() {
    let request =
        KeySyncRequest { pm_uid: "12345678910".to_string(), key_encryption_key: vec![1, 2, 3] };
    println!("Serailization {:?}", serde_json::to_string(&request));
    let json_str = r#"{"keyEncryptionKey":"AQID","pmUid":"12345678910"}"#;
    let request_from_string_num = serde_json::from_str::<KeySyncRequest>(json_str).unwrap();
    assert_eq!(request.encode_to_vec(), request_from_string_num.encode_to_vec());
}

#[tokio::test]
async fn test_embedding_search() {
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

    let pm_uid = 234.to_string();
    let boot_strap_request = BootStrapRequest {
        key_encryption_key: TEST_EK.to_vec(),
        pm_uid: pm_uid.clone(),
        boot_strap_info: Some(KeyDerivationInfo::default()),
    };
    send_plantext_request(&mut tx, &mut client_session, boot_strap_request);
    let boot_strap_response: BootStrapResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    assert_eq!(boot_strap_response.status, boot_strap_response::Status::Success as i32);
    // Key sync
    let request_id = 0xeadbeef;
    let key_sync_request = KeySyncRequest { key_encryption_key: TEST_EK.to_vec(), pm_uid };
    send_plantext_request_with_id(&mut tx, &mut client_session, key_sync_request, request_id);

    let (_key_sync_response, return_id): (KeySyncResponse, i32) =
        receive_plaintext_response_with_id(&mut response_stream, &mut client_session).await;
    assert_eq!(request_id, return_id);

    let embedding1 =
        Embedding { model_signature: "test_model".to_string(), values: vec![1.0, 0.0, 0.0] };
    let embedding2 =
        Embedding { model_signature: "test_model2".to_string(), values: vec![0.0, 1.0, 0.0] };
    let request1 = AddMemoryRequest {
        memory: Some(Memory {
            id: "".to_string(),
            content: "this is a test".as_bytes().to_vec(),
            embeddings: vec![embedding1, embedding2],
            ..Default::default()
        }),
    };
    send_plantext_request(&mut tx, &mut client_session, request1);

    let add_memory_response1: AddMemoryResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    let embedding3 =
        Embedding { model_signature: "test_model".to_string(), values: vec![1.0, 0.0, 0.0] };
    let embedding4 =
        Embedding { model_signature: "test_model".to_string(), values: vec![0.0, 1.0, 0.0] };
    let request2 = AddMemoryRequest {
        memory: Some(Memory {
            id: "".to_string(),
            content: "this is a test".as_bytes().to_vec(),
            embeddings: vec![embedding3, embedding4],
            ..Default::default()
        }),
    };
    send_plantext_request(&mut tx, &mut client_session, request2);

    let add_memory_response2: AddMemoryResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    let search_embedding =
        Embedding { model_signature: "test_model".to_string(), values: vec![1.0, 1.0, 0.0] };
    let search_request =
        SearchMemoryRequest { embedding_query: vec![search_embedding], ..Default::default() };
    send_plantext_request(&mut tx, &mut client_session, search_request);

    let search_memory_response: SearchMemoryResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    assert_eq!(search_memory_response.results.len(), 2);

    // memory2 will have score [1.0, 0, 0] x [1.0, 1.0, 0] + [0.0, 1.0, 0.0] x [1.0,
    // 1.0, 0.0] = 2.0 memory1 will have score [0.0, 1.0, 0.0] x [1.0, 1.0, 0.0]
    // = 1.0
    assert_eq!(search_memory_response.results[0].score, 2.0);
    assert_eq!(search_memory_response.results[1].score, 1.0);
    assert_eq!(
        search_memory_response.results[0].memory.as_ref().unwrap().id,
        add_memory_response2.id
    );
    assert_eq!(
        search_memory_response.results[1].memory.as_ref().unwrap().id,
        add_memory_response1.id
    );
}

#[tokio::test]
async fn test_boot_strap() {
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

    let pm_uid = 234.to_string();
    let boot_strap_request = BootStrapRequest {
        key_encryption_key: TEST_EK.to_vec(),
        pm_uid: pm_uid.clone(),
        boot_strap_info: Some(KeyDerivationInfo::default()),
    };
    send_plantext_request(&mut tx, &mut client_session, boot_strap_request.clone());
    let boot_strap_response: BootStrapResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    assert_eq!(boot_strap_response.status, boot_strap_response::Status::Success as i32);

    // Register again.
    send_plantext_request(&mut tx, &mut client_session, boot_strap_request);
    let boot_strap_response: BootStrapResponse =
        receive_plaintext_response(&mut response_stream, &mut client_session).await;

    assert_eq!(boot_strap_response.status, boot_strap_response::Status::UserAlreadyExists as i32);
}
