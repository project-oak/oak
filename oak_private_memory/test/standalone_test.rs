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
    key_sync_response, memory_value, sealed_memory_response, search_memory_query,
    user_registration_response, AddMemoryRequest, AddMemoryResponse, Embedding, EmbeddingQuery,
    GetMemoriesRequest, GetMemoriesResponse, GetMemoryByIdRequest, GetMemoryByIdResponse,
    InvalidRequestResponse, KeyDerivationInfo, KeySyncRequest, KeySyncResponse, Memory,
    MemoryContent, MemoryValue, ResetMemoryRequest, ResetMemoryResponse, ScoreRange,
    SealedMemoryResponse, SearchMemoryQuery, SearchMemoryRequest, SearchMemoryResponse,
    UserRegistrationRequest, UserRegistrationResponse,
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

#[derive(Clone, Copy, Debug)]
enum TestMode {
    BinaryProto,
    Json,
}

// Generic helper to send a request based on TestMode
async fn send_request_generic<T>(
    tx: &mut mpsc::Sender<SessionRequest>,
    client_session: &mut oak_session::ClientSession,
    request_data: T,
    request_id: Option<i32>,
    mode: TestMode,
) where
    T: RequestUnpacking,
{
    let mut sealed_memory_request = request_data.into_request();
    if let Some(id) = request_id {
        sealed_memory_request.request_id = id;
    }

    let payload = match mode {
        TestMode::BinaryProto => sealed_memory_request.encode_to_vec(),
        TestMode::Json => {
            serde_json::to_vec(&sealed_memory_request).expect("JSON serialization failed")
        }
    };

    let encrypted_request =
        client_session.encrypt_request(&payload).expect("failed to encrypt message");
    tx.try_send(encrypted_request).expect("Could not send request to server");
}

// Generic helper to receive a response based on TestMode
async fn receive_response_generic<T>(
    response_stream: &mut tonic::Streaming<SessionResponse>,
    client_session: &mut oak_session::ClientSession,
    mode: TestMode,
) -> (T, i32)
// Returns (SpecificResponse, request_id)
where
    T: ResponsePacking,
{
    let response = response_stream
        .message()
        .await
        .expect("error getting response")
        .expect("didn't get any repsonse");

    let decrypted_response =
        client_session.decrypt_response(response).expect("failed to decrypt response");

    let sealed_memory_response = match mode {
        TestMode::BinaryProto => SealedMemoryResponse::decode(decrypted_response.as_ref())
            .expect("Not a valid proto response"),
        TestMode::Json => serde_json::from_slice::<SealedMemoryResponse>(&decrypted_response)
            .expect("Not a valid JSON response"),
    };
    let request_id = sealed_memory_response.request_id;
    let specific_response =
        T::from_response(sealed_memory_response).expect("A different type of response was parsed!");

    (specific_response, request_id)
}

async fn execute_add_get_reset_memory_logic(
    tx: &mut mpsc::Sender<SessionRequest>,
    client_session: &mut oak_session::ClientSession,
    response_stream: &mut tonic::Streaming<SessionResponse>,
    mode: TestMode,
) {
    let pm_uid = format!(
        "test_add_get_reset_{:?}_{}",
        mode,
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    );

    // User Registration
    let user_registration_request = UserRegistrationRequest {
        key_encryption_key: TEST_EK.to_vec(),
        pm_uid: pm_uid.clone(),
        boot_strap_info: Some(KeyDerivationInfo::default()),
    };
    send_request_generic(tx, client_session, user_registration_request, None, mode).await;
    let (user_reg_response, _): (UserRegistrationResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(user_reg_response.status, user_registration_response::Status::Success as i32);

    // Key Sync
    let key_sync_request_id = 0xeadbeef;
    let key_sync_request_data =
        KeySyncRequest { key_encryption_key: TEST_EK.to_vec(), pm_uid: pm_uid.clone() };
    send_request_generic(
        tx,
        client_session,
        key_sync_request_data,
        Some(key_sync_request_id),
        mode,
    )
    .await;
    let (key_sync_response, returned_id): (KeySyncResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(returned_id, key_sync_request_id);
    assert_eq!(key_sync_response.status, key_sync_response::Status::Success as i32);

    // AddMemoryRequest
    let mut contents_map = std::collections::HashMap::new();
    contents_map.insert(
        "text_data".to_string(),
        MemoryValue {
            value: Some(memory_value::Value::BytesVal("this is a test".as_bytes().to_vec())),
        },
    );
    let add_memory_request_data = AddMemoryRequest {
        memory: Some(Memory {
            id: "".to_string(),
            content: Some(MemoryContent { contents: contents_map }),
            tags: vec!["tag".to_string()],
            ..Default::default()
        }),
    };
    send_request_generic(tx, client_session, add_memory_request_data, None, mode).await;
    let (add_memory_response, _): (AddMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    let memory_id_from_add = add_memory_response.id;

    // GetMemoriesRequest
    let get_memories_request_data = GetMemoriesRequest { tag: "tag".to_string() };
    send_request_generic(tx, client_session, get_memories_request_data, None, mode).await;
    let (get_memories_response_1, _): (GetMemoriesResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(get_memories_response_1.memories.len(), 1);

    let memory_content = get_memories_response_1.memories[0].content.clone().unwrap();
    assert_eq!(memory_content.contents.len(), 1);
    let memory_value = memory_content.contents["text_data"].value.clone().unwrap();
    let memory_value = match memory_value {
        memory_value::Value::BytesVal(bytes) => bytes,
        _ => vec![],
    };
    assert_eq!(memory_value, "this is a test".as_bytes().to_vec());

    // GetMemoryByIdRequest
    let get_memory_by_id_request_data = GetMemoryByIdRequest { id: memory_id_from_add.clone() };
    send_request_generic(tx, client_session, get_memory_by_id_request_data, None, mode).await;
    let (get_memory_by_id_response, _): (GetMemoryByIdResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert!(get_memory_by_id_response.memory.is_some());
    assert_eq!(
        get_memories_response_1.memories[0].encode_to_vec(),
        get_memory_by_id_response.memory.unwrap().encode_to_vec()
    );

    // ResetMemoryRequest
    let reset_memory_request_data = ResetMemoryRequest::default();
    send_request_generic(tx, client_session, reset_memory_request_data, None, mode).await;
    let (reset_memory_response, _): (ResetMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert!(reset_memory_response.success);

    // GetMemoriesRequest again
    let get_memories_request_data_2 = GetMemoriesRequest { tag: "tag".to_string() };
    send_request_generic(tx, client_session, get_memories_request_data_2, None, mode).await;
    let (get_memories_response_2, _): (GetMemoriesResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(get_memories_response_2.memories.len(), 0);
}

async fn execute_embedding_search_logic(
    tx: &mut mpsc::Sender<SessionRequest>,
    client_session: &mut oak_session::ClientSession,
    response_stream: &mut tonic::Streaming<SessionResponse>,
    mode: TestMode,
) {
    let pm_uid = format!(
        "test_embedding_search_{:?}_{}",
        mode,
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    );

    // User Registration
    let user_registration_request = UserRegistrationRequest {
        key_encryption_key: TEST_EK.to_vec(),
        pm_uid: pm_uid.clone(),
        boot_strap_info: Some(KeyDerivationInfo::default()),
    };
    send_request_generic(tx, client_session, user_registration_request, None, mode).await;
    let (user_reg_response, _): (UserRegistrationResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(user_reg_response.status, user_registration_response::Status::Success as i32);

    // Key Sync
    let key_sync_request_id = 0xeadbeef;
    let key_sync_request_data = KeySyncRequest { key_encryption_key: TEST_EK.to_vec(), pm_uid };
    send_request_generic(
        tx,
        client_session,
        key_sync_request_data,
        Some(key_sync_request_id),
        mode,
    )
    .await;
    let (_key_sync_response, returned_id): (KeySyncResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(returned_id, key_sync_request_id);

    let embedding1 =
        Embedding { identifier: "test_model".to_string(), values: vec![1.0, 0.0, 0.0] };
    let embedding2 =
        Embedding { identifier: "test_model2".to_string(), values: vec![0.0, 1.0, 0.0] };
    let mut contents_map1 = std::collections::HashMap::new();
    contents_map1.insert(
        "item_text_1".to_string(),
        MemoryValue {
            value: Some(memory_value::Value::BytesVal("this is a test item 1".as_bytes().to_vec())),
        },
    );
    let request1 = AddMemoryRequest {
        memory: Some(Memory {
            id: "".to_string(),
            content: Some(MemoryContent { contents: contents_map1 }),
            embeddings: vec![embedding1, embedding2],
            tags: Vec::new(),
        }),
    };
    send_request_generic(tx, client_session, request1, None, mode).await;
    let (add_memory_response1, _): (AddMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;

    let embedding3 =
        Embedding { identifier: "test_model".to_string(), values: vec![1.0, 0.0, 0.0] };
    let embedding4 =
        Embedding { identifier: "test_model".to_string(), values: vec![0.0, 1.0, 0.0] };
    let mut contents_map2 = std::collections::HashMap::new();
    contents_map2.insert(
        "item_text_2".to_string(),
        MemoryValue {
            value: Some(memory_value::Value::BytesVal("this is a test item 2".as_bytes().to_vec())),
        },
    );
    let request2 = AddMemoryRequest {
        memory: Some(Memory {
            id: "".to_string(),
            content: Some(MemoryContent { contents: contents_map2 }),
            embeddings: vec![embedding3, embedding4],
            tags: Vec::new(),
        }),
    };
    send_request_generic(tx, client_session, request2, None, mode).await;
    let (add_memory_response2, _): (AddMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;

    let search_embedding =
        Embedding { identifier: "test_model".to_string(), values: vec![1.0, 1.0, 0.0] };
    let embedding_query =
        EmbeddingQuery { embedding: vec![search_embedding], ..Default::default() };
    let search_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::EmbeddingQuery(embedding_query)),
    };
    let search_request = SearchMemoryRequest { query: Some(search_query) };
    send_request_generic(tx, client_session, search_request, None, mode).await;
    let (search_memory_response, _): (SearchMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;

    assert_eq!(search_memory_response.results.len(), 2);
    assert_eq!(
        search_memory_response.results[0].memory.as_ref().unwrap().id,
        add_memory_response2.id
    );
    assert_eq!(
        search_memory_response.results[1].memory.as_ref().unwrap().id,
        add_memory_response1.id
    );

    // memory2 will have score [0, 1.0, 0] x [1.0, 2.0, 0] = 2.0 (the second
    // embedding got filtered out because it has score 1.0 < 1.5) memory1 is
    // filtered out because its only embedding has score 1.0 < 1.5
    let search_embedding =
        Embedding { identifier: "test_model".to_string(), values: vec![1.0, 2.0, 0.0] };
    let score_range = ScoreRange { min: 2.0, max: 3.0 };
    let embedding_query = EmbeddingQuery {
        embedding: vec![search_embedding],
        score_range: Some(score_range),
        ..Default::default()
    };
    let search_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::EmbeddingQuery(embedding_query)),
    };
    let search_request = SearchMemoryRequest { query: Some(search_query) };
    send_request_generic(tx, client_session, search_request, None, mode).await;
    let (search_memory_response, _): (SearchMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;

    assert_eq!(search_memory_response.results.len(), 1);
    assert_eq!(
        search_memory_response.results[0].memory.as_ref().unwrap().id,
        add_memory_response2.id
    );
}

async fn execute_boot_strap_logic(
    tx: &mut mpsc::Sender<SessionRequest>,
    client_session: &mut oak_session::ClientSession,
    response_stream: &mut tonic::Streaming<SessionResponse>,
    mode: TestMode,
) {
    let pm_uid = format!(
        "test_bootstrap_{:?}_{}",
        mode,
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    );

    let user_registration_request = UserRegistrationRequest {
        key_encryption_key: TEST_EK.to_vec(),
        pm_uid: pm_uid.clone(),
        boot_strap_info: Some(KeyDerivationInfo::default()),
    };

    // First registration: Success
    send_request_generic(tx, client_session, user_registration_request.clone(), None, mode).await;
    let (user_reg_response1, _): (UserRegistrationResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(user_reg_response1.status, user_registration_response::Status::Success as i32);

    // Second registration: UserAlreadyExists
    send_request_generic(tx, client_session, user_registration_request, None, mode).await;
    let (user_reg_response2, _): (UserRegistrationResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(
        user_reg_response2.status,
        user_registration_response::Status::UserAlreadyExists as i32
    );
    assert!(user_reg_response2.key_derivation_info.is_some());
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
async fn test_add_get_reset_memory_all_modes() {
    let (addr, _db_addr, _server_join_handle, _db_join_handle) = start_server().await.unwrap();
    let url = format!("http://{addr}");

    for &mode in [TestMode::BinaryProto, TestMode::Json].iter() {
        println!("Testing Add/Get/Reset in {:?} mode", mode);
        let channel = Channel::from_shared(url.clone()).unwrap().connect().await.unwrap();
        let mut client = SealedMemoryServiceClient::new(channel);
        let (mut tx, rx) = mpsc::channel(10);
        let mut response_stream = client.invoke(rx).await.unwrap().into_inner();
        let mut client_session = oak_session::ClientSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .unwrap();
        client_session.init_session(&mut tx, &mut response_stream).await.unwrap();

        execute_add_get_reset_memory_logic(
            &mut tx,
            &mut client_session,
            &mut response_stream,
            mode,
        )
        .await;
    }
}

#[tokio::test]
async fn test_embedding_search_all_modes() {
    let (addr, _db_addr, _server_join_handle, _db_join_handle) = start_server().await.unwrap();
    let url = format!("http://{addr}");

    for &mode in [TestMode::BinaryProto, TestMode::Json].iter() {
        println!("Testing Embedding Search in {:?} mode", mode);
        let channel = Channel::from_shared(url.clone()).unwrap().connect().await.unwrap();
        let mut client = SealedMemoryServiceClient::new(channel);
        let (mut tx, rx) = mpsc::channel(10);
        let mut response_stream = client.invoke(rx).await.unwrap().into_inner();
        let mut client_session = oak_session::ClientSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .unwrap();
        client_session.init_session(&mut tx, &mut response_stream).await.unwrap();

        execute_embedding_search_logic(&mut tx, &mut client_session, &mut response_stream, mode)
            .await;
    }
}

#[tokio::test]
async fn test_boot_strap_all_modes() {
    let (addr, _db_addr, _server_join_handle, _db_join_handle) = start_server().await.unwrap();
    let url = format!("http://{addr}");

    for &mode in [TestMode::BinaryProto, TestMode::Json].iter() {
        println!("Testing Bootstrap in {:?} mode", mode);
        let channel = Channel::from_shared(url.clone()).unwrap().connect().await.unwrap();
        let mut client = SealedMemoryServiceClient::new(channel);
        let (mut tx, rx) = mpsc::channel(10);
        let mut response_stream = client.invoke(rx).await.unwrap().into_inner();
        let mut client_session = oak_session::ClientSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .unwrap();
        client_session.init_session(&mut tx, &mut response_stream).await.unwrap();

        execute_boot_strap_logic(&mut tx, &mut client_session, &mut response_stream, mode).await;
    }
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
