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

use anyhow::Result;
use futures::channel::mpsc;
use log::info;
use oak_session::{
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
    Session,
};
use private_memory_server_lib::{
    app::{run_persistence_service, RequestUnpacking, ResponsePacking},
    app_config::ApplicationConfig,
};
use prost::Message;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_service_client::SealedMemoryServiceClient;
use sealed_memory_rust_proto::prelude::v1::*;
use tokio::{net::TcpListener, sync::mpsc as tokio_mpsc};
use tonic::transport::Channel;
fn init_logging() {
    let _ = env_logger::builder().is_test(true).try_init();
}

static TEST_EK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";
async fn start_server() -> Result<(
    SocketAddr,
    SocketAddr,
    tokio::task::JoinHandle<Result<()>>,
    tokio::task::JoinHandle<Result<()>>,
    tokio::task::JoinHandle<()>,
)> {
    init_logging();
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await?;
    let addr = listener.local_addr()?;

    let db_addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let db_listener = TcpListener::bind(db_addr).await?;
    let db_addr = db_listener.local_addr()?;

    let application_config = ApplicationConfig { database_service_host: db_addr };

    let application_config_vec = serde_json::to_vec(&application_config)?;

    let metrics = private_memory_server_lib::metrics::get_global_metrics();
    let (persistence_tx, persistence_rx) = tokio_mpsc::unbounded_channel();
    let persistence_join_handle = tokio::spawn(run_persistence_service(persistence_rx));
    Ok((
        addr,
        db_addr,
        tokio::spawn(private_memory_server_lib::app_service::create(
            listener,
            private_memory_server_lib::app::SealedMemoryHandler::new(
                &application_config_vec,
                metrics.clone(),
                persistence_tx,
            )
            .await,
            metrics,
        )),
        tokio::spawn(private_memory_test_database_server_lib::service::create(db_listener)),
        persistence_join_handle,
    ))
}

#[derive(Clone, Copy, Debug)]
enum TestMode {
    BinaryProto,
    Json,
}

// Generic helper to send a request based on TestMode
async fn send_request_generic<T>(
    tx: &mut mpsc::Sender<SealedMemorySessionRequest>,
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

    let encrypted_request = client_session.encrypt(payload).expect("failed to encrypt message");
    tx.try_send(SealedMemorySessionRequest { session_request: Some(encrypted_request) })
        .expect("Could not send request to server");
}

// Generic helper to receive a response based on TestMode
async fn receive_response_generic<T>(
    response_stream: &mut tonic::Streaming<SealedMemorySessionResponse>,
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

    let decrypted_response = client_session
        .decrypt(response.session_response.expect("empty session response"))
        .expect("failed to decrypt response");

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
    tx: &mut mpsc::Sender<SealedMemorySessionRequest>,
    client_session: &mut oak_session::ClientSession,
    response_stream: &mut tonic::Streaming<SealedMemorySessionResponse>,
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
    contents_map.insert(
        "string_data".to_string(),
        MemoryValue {
            value: Some(memory_value::Value::StringVal("this is a test string".to_string())),
        },
    );
    contents_map.insert(
        "int64_data".to_string(),
        MemoryValue { value: Some(memory_value::Value::Int64Val(123456789)) },
    );
    let add_memory_request_data = AddMemoryRequest {
        memory: Some(Memory {
            id: "".to_string(),
            content: Some(MemoryContent { contents: contents_map }),
            tags: vec!["tag".to_string()],
            ..Default::default()
        }),
    };
    send_request_generic(tx, client_session, add_memory_request_data.clone(), None, mode).await;
    let (add_memory_response, _): (AddMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    let memory_id_from_add = add_memory_response.id;
    send_request_generic(tx, client_session, add_memory_request_data, None, mode).await;
    let _: (AddMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;

    // GetMemoriesRequest
    let get_memories_request_data =
        GetMemoriesRequest { tag: "tag".to_string(), page_size: 1, result_mask: None };
    send_request_generic(tx, client_session, get_memories_request_data, None, mode).await;
    let (get_memories_response_1, _): (GetMemoriesResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(get_memories_response_1.memories.len(), 1);

    let memory_content = get_memories_response_1.memories[0].content.clone().unwrap();
    assert_eq!(memory_content.contents.len(), 3);
    let memory_value = memory_content.contents["text_data"].value.clone().unwrap();
    let memory_value = match memory_value {
        memory_value::Value::BytesVal(bytes) => bytes,
        _ => vec![],
    };
    assert_eq!(memory_value, "this is a test".as_bytes().to_vec());
    let memory_value = memory_content.contents["string_data"].value.clone().unwrap();
    let memory_value = match memory_value {
        memory_value::Value::StringVal(string) => string,
        _ => "".to_string(),
    };
    assert_eq!(memory_value, "this is a test string");
    let memory_value = memory_content.contents["int64_data"].value.clone().unwrap();
    let memory_value = match memory_value {
        memory_value::Value::Int64Val(int64) => int64,
        _ => 0,
    };
    assert_eq!(memory_value, 123456789);

    // GetMemoryByIdRequest
    let get_memory_by_id_request_data =
        GetMemoryByIdRequest { id: memory_id_from_add.clone(), result_mask: None };
    send_request_generic(tx, client_session, get_memory_by_id_request_data, None, mode).await;
    let (get_memory_by_id_response, _): (GetMemoryByIdResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert!(get_memory_by_id_response.memory.is_some());
    assert_eq!(memory_id_from_add, get_memory_by_id_response.memory.unwrap().id);

    // ResetMemoryRequest
    let reset_memory_request_data = ResetMemoryRequest::default();
    send_request_generic(tx, client_session, reset_memory_request_data, None, mode).await;
    let (reset_memory_response, _): (ResetMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert!(reset_memory_response.success);

    // GetMemoriesRequest again
    let get_memories_request_data_2 =
        GetMemoriesRequest { tag: "tag".to_string(), page_size: 10, result_mask: None };
    send_request_generic(tx, client_session, get_memories_request_data_2, None, mode).await;
    let (get_memories_response_2, _): (GetMemoriesResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(get_memories_response_2.memories.len(), 0);
}

async fn execute_delete_memory_logic(
    tx: &mut mpsc::Sender<SealedMemorySessionRequest>,
    client_session: &mut oak_session::ClientSession,
    response_stream: &mut tonic::Streaming<SealedMemorySessionResponse>,
    mode: TestMode,
) {
    let pm_uid = format!(
        "test_delete_{:?}_{}",
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
    let key_sync_request_data =
        KeySyncRequest { key_encryption_key: TEST_EK.to_vec(), pm_uid: pm_uid.clone() };
    send_request_generic(tx, client_session, key_sync_request_data, None, mode).await;
    let (key_sync_response, _): (KeySyncResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(key_sync_response.status, key_sync_response::Status::Success as i32);

    // Add a few memory items
    let mut added_memory_ids = Vec::new();
    for i in 0..3 {
        let add_memory_request_data = AddMemoryRequest {
            memory: Some(Memory {
                id: "".to_string(), // Let server generate ID
                content: None,
                tags: vec![format!("delete_tag_{}", i)],
                ..Default::default()
            }),
        };
        send_request_generic(tx, client_session, add_memory_request_data, None, mode).await;
        let (add_memory_response, _): (AddMemoryResponse, i32) =
            receive_response_generic(response_stream, client_session, mode).await;
        added_memory_ids.push(add_memory_response.id);
    }

    // Verify items were added
    for id in &added_memory_ids {
        let get_memory_by_id_request_data =
            GetMemoryByIdRequest { id: id.clone(), result_mask: None };
        send_request_generic(tx, client_session, get_memory_by_id_request_data, None, mode).await;
        let (get_memory_by_id_response, _): (GetMemoryByIdResponse, i32) =
            receive_response_generic(response_stream, client_session, mode).await;
        assert!(get_memory_by_id_response.success);
        assert!(get_memory_by_id_response.memory.is_some());
        assert_eq!(get_memory_by_id_response.memory.unwrap().id, *id);
    }

    // Delete some of the memory items
    let ids_to_delete = vec![added_memory_ids[0].clone(), added_memory_ids[2].clone()];
    let delete_memory_request_data = DeleteMemoryRequest { ids: ids_to_delete.clone() };
    send_request_generic(tx, client_session, delete_memory_request_data, None, mode).await;
    let (delete_memory_response, _): (DeleteMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert!(delete_memory_response.success);

    // Verify deleted items are gone
    for id in &ids_to_delete {
        let get_memory_by_id_request_data =
            GetMemoryByIdRequest { id: id.clone(), result_mask: None };
        send_request_generic(tx, client_session, get_memory_by_id_request_data, None, mode).await;
        let (get_memory_by_id_response, _): (GetMemoryByIdResponse, i32) =
            receive_response_generic(response_stream, client_session, mode).await;
        assert!(!get_memory_by_id_response.success);
        assert!(get_memory_by_id_response.memory.is_none());
    }

    // Verify the item that was NOT deleted still exists
    let id_not_deleted = added_memory_ids[1].clone();
    let get_memory_by_id_request_data =
        GetMemoryByIdRequest { id: id_not_deleted.clone(), result_mask: None };
    send_request_generic(tx, client_session, get_memory_by_id_request_data, None, mode).await;
    let (get_memory_by_id_response, _): (GetMemoryByIdResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert!(get_memory_by_id_response.success);
    assert!(get_memory_by_id_response.memory.is_some());
    assert_eq!(get_memory_by_id_response.memory.unwrap().id, id_not_deleted);

    // Attempt to delete a non-existent ID
    let non_existent_id = "non_existent_memory_id".to_string();
    let delete_memory_request_data_non_existent =
        DeleteMemoryRequest { ids: vec![non_existent_id.clone()] };
    send_request_generic(tx, client_session, delete_memory_request_data_non_existent, None, mode)
        .await;
    let (delete_memory_response_non_existent, _): (DeleteMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert!(!delete_memory_response_non_existent.success);
}

async fn execute_embedding_search_logic(
    tx: &mut mpsc::Sender<SealedMemorySessionRequest>,
    client_session: &mut oak_session::ClientSession,
    response_stream: &mut tonic::Streaming<SealedMemorySessionResponse>,
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
    let search_request =
        SearchMemoryRequest { query: Some(search_query), page_size: 10, ..Default::default() };
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
    let search_request =
        SearchMemoryRequest { query: Some(search_query), page_size: 10, ..Default::default() };
    send_request_generic(tx, client_session, search_request, None, mode).await;
    let (search_memory_response, _): (SearchMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;

    assert_eq!(search_memory_response.results.len(), 1);
    assert_eq!(
        search_memory_response.results[0].memory.as_ref().unwrap().id,
        add_memory_response2.id
    );
}

async fn execute_get_masking_logic(
    tx: &mut mpsc::Sender<SealedMemorySessionRequest>,
    client_session: &mut oak_session::ClientSession,
    response_stream: &mut tonic::Streaming<SealedMemorySessionResponse>,
    mode: TestMode,
) {
    let pm_uid = format!(
        "test_get_masking_{:?}_{}",
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
    let key_sync_request_data =
        KeySyncRequest { key_encryption_key: TEST_EK.to_vec(), pm_uid: pm_uid.clone() };
    send_request_generic(tx, client_session, key_sync_request_data, None, mode).await;
    let (key_sync_response, _): (KeySyncResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(key_sync_response.status, key_sync_response::Status::Success as i32);

    // Add a comprehensive memory item
    let original_memory_id = "mask_test_mem_item_id_1".to_string();
    let original_tags = vec!["tagMaskTestA".to_string(), "tagMaskTestB".to_string()];
    let original_embedding =
        Embedding { identifier: "mask_test_model".to_string(), values: vec![0.5, 0.5] };
    let original_embeddings = vec![original_embedding.clone()];

    let mut original_contents_map = std::collections::HashMap::new();
    original_contents_map.insert(
        "content_key_str".to_string(),
        MemoryValue {
            value: Some(memory_value::Value::BytesVal("value_string_data".as_bytes().to_vec())),
        },
    );
    original_contents_map.insert(
        "content_key_int".to_string(),
        MemoryValue { value: Some(memory_value::Value::Int64Val(98765)) },
    );
    let original_memory_content = MemoryContent { contents: original_contents_map.clone() };

    let add_memory_request_data = AddMemoryRequest {
        memory: Some(Memory {
            id: original_memory_id.clone(),
            tags: original_tags.clone(),
            embeddings: original_embeddings.clone(),
            content: Some(original_memory_content.clone()),
        }),
    };
    send_request_generic(tx, client_session, add_memory_request_data, None, mode).await;
    let (add_memory_response, _): (AddMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(add_memory_response.id, original_memory_id);

    // Test GetMemoryById with a mask
    info!("Test GetMemoryById with a mask");
    let get_memory_by_id_request = GetMemoryByIdRequest {
        id: original_memory_id.clone(),
        result_mask: Some(ResultMask {
            include_fields: vec![MemoryField::Id as i32, MemoryField::Tags as i32],
            include_content_fields: vec![],
        }),
    };
    send_request_generic(tx, client_session, get_memory_by_id_request, None, mode).await;
    let (get_memory_by_id_response, _): (GetMemoryByIdResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert!(get_memory_by_id_response.success);
    let mem_id_tags = get_memory_by_id_response.memory.as_ref().unwrap();
    assert_eq!(mem_id_tags.id, original_memory_id);
    assert_eq!(mem_id_tags.tags, original_tags);
    assert!(mem_id_tags.embeddings.is_empty());
    assert!(mem_id_tags.content.is_none());

    // Test GetMemories with a mask
    info!("Test GetMemories with a mask");
    let get_memories_request = GetMemoriesRequest {
        tag: "tagMaskTestA".to_string(),
        page_size: 1,
        result_mask: Some(ResultMask {
            include_fields: vec![MemoryField::Content as i32],
            include_content_fields: vec!["content_key_str".to_string()],
        }),
    };
    send_request_generic(tx, client_session, get_memories_request, None, mode).await;
    let (get_memories_response, _): (GetMemoriesResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(get_memories_response.memories.len(), 1);
    let mem_cs = &get_memories_response.memories[0];
    assert!(mem_cs.id.is_empty());
    assert!(mem_cs.tags.is_empty());
    assert!(mem_cs.embeddings.is_empty());
    assert!(mem_cs.content.is_some());
    let specific_contents = &mem_cs.content.as_ref().unwrap().contents;
    assert_eq!(specific_contents.len(), 1);
    assert!(specific_contents.contains_key("content_key_str"));
    assert_eq!(specific_contents["content_key_str"], original_contents_map["content_key_str"]);
}

async fn execute_result_masking_logic(
    tx: &mut mpsc::Sender<SealedMemorySessionRequest>,
    client_session: &mut oak_session::ClientSession,
    response_stream: &mut tonic::Streaming<SealedMemorySessionResponse>,
    mode: TestMode,
) {
    let pm_uid = format!(
        "test_result_masking_{:?}_{}",
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
    let key_sync_request_data =
        KeySyncRequest { key_encryption_key: TEST_EK.to_vec(), pm_uid: pm_uid.clone() };
    send_request_generic(tx, client_session, key_sync_request_data, None, mode).await;
    let (key_sync_response, _): (KeySyncResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(key_sync_response.status, key_sync_response::Status::Success as i32);

    // Add a comprehensive memory item
    let original_memory_id = "mask_test_mem_item_id_1".to_string();
    let original_tags = vec!["tagMaskTestA".to_string(), "tagMaskTestB".to_string()];
    let original_embedding =
        Embedding { identifier: "mask_test_model".to_string(), values: vec![0.5, 0.5] };
    let original_embeddings = vec![original_embedding.clone()];

    let mut original_contents_map = std::collections::HashMap::new();
    original_contents_map.insert(
        "content_key_str".to_string(),
        MemoryValue {
            value: Some(memory_value::Value::BytesVal("value_string_data".as_bytes().to_vec())),
        },
    );
    original_contents_map.insert(
        "content_key_int".to_string(),
        MemoryValue { value: Some(memory_value::Value::Int64Val(98765)) },
    );
    let original_memory_content = MemoryContent { contents: original_contents_map.clone() };

    let add_memory_request_data = AddMemoryRequest {
        memory: Some(Memory {
            id: original_memory_id.clone(),
            tags: original_tags.clone(),
            embeddings: original_embeddings.clone(),
            content: Some(original_memory_content.clone()),
        }),
    };
    send_request_generic(tx, client_session, add_memory_request_data, None, mode).await;
    let (add_memory_response, _): (AddMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(add_memory_response.id, original_memory_id);

    // Search query that will find the item
    let search_embedding_for_query = Embedding {
        identifier: "mask_test_model".to_string(), // Match identifier
        values: vec![0.5, 0.5],
    };
    let embedding_query_for_search = EmbeddingQuery {
        embedding: vec![search_embedding_for_query.clone()],
        ..Default::default()
    };
    let search_query_clause = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::EmbeddingQuery(
            embedding_query_for_search.clone(),
        )),
    };

    // Test Case 1: No ResultMask (result_mask field is None)
    info!("Test Case 1: No ResultMask (all fields expected)");
    let search_request_no_mask = SearchMemoryRequest {
        query: Some(search_query_clause.clone()),
        page_size: 1,
        result_mask: None,
    };
    send_request_generic(tx, client_session, search_request_no_mask, None, mode).await;
    let (response_no_mask, _): (SearchMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(response_no_mask.results.len(), 1);
    let mem_no_mask = response_no_mask.results[0].memory.as_ref().unwrap();
    assert_eq!(mem_no_mask.id, original_memory_id);
    assert_eq!(mem_no_mask.tags, original_tags);
    assert_eq!(mem_no_mask.embeddings, original_embeddings);
    assert_eq!(mem_no_mask.content.as_ref().unwrap().contents, original_contents_map);

    // Test Case 2: Empty include_fields (no top-level fields expected)
    info!("Test Case 2: Empty include_fields");
    let search_request_empty_fields = SearchMemoryRequest {
        query: Some(search_query_clause.clone()),
        page_size: 1,
        result_mask: Some(ResultMask { include_fields: vec![], include_content_fields: vec![] }),
    };
    send_request_generic(tx, client_session, search_request_empty_fields, None, mode).await;
    let (response_empty_fields, _): (SearchMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(response_empty_fields.results.len(), 1);
    let mem_empty_fields = response_empty_fields.results[0].memory.as_ref().unwrap();
    assert!(mem_empty_fields.id.is_empty(), "ID should be empty");
    assert!(mem_empty_fields.tags.is_empty(), "Tags should be empty");
    assert!(mem_empty_fields.embeddings.is_empty(), "Embeddings should be empty");
    assert!(mem_empty_fields.content.is_none(), "Content should be None");

    // Test Case 3: Specific top-level fields (ID and TAGS)
    info!("Test Case 3: Specific top-level fields (ID and TAGS)");
    let search_request_id_tags = SearchMemoryRequest {
        query: Some(search_query_clause.clone()),
        page_size: 1,
        result_mask: Some(ResultMask {
            include_fields: vec![MemoryField::Id as i32, MemoryField::Tags as i32],
            include_content_fields: vec![],
        }),
    };
    send_request_generic(tx, client_session, search_request_id_tags, None, mode).await;
    let (response_id_tags, _): (SearchMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(response_id_tags.results.len(), 1);
    let mem_id_tags = response_id_tags.results[0].memory.as_ref().unwrap();
    assert_eq!(mem_id_tags.id, original_memory_id);
    assert_eq!(mem_id_tags.tags, original_tags);
    assert!(mem_id_tags.embeddings.is_empty());
    assert!(mem_id_tags.content.is_none());

    // Test Case 4: CONTENT included, specific content_fields ("content_key_str")
    info!("Test Case 4: CONTENT with specific content_fields");
    let search_request_content_specific = SearchMemoryRequest {
        query: Some(search_query_clause.clone()),
        page_size: 1,
        result_mask: Some(ResultMask {
            include_fields: vec![MemoryField::Content as i32],
            include_content_fields: vec!["content_key_str".to_string()],
        }),
    };
    send_request_generic(tx, client_session, search_request_content_specific, None, mode).await;
    let (response_content_specific, _): (SearchMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(response_content_specific.results.len(), 1);
    let mem_cs = response_content_specific.results[0].memory.as_ref().unwrap();
    assert!(mem_cs.id.is_empty());
    assert!(mem_cs.tags.is_empty());
    assert!(mem_cs.embeddings.is_empty());
    assert!(mem_cs.content.is_some());
    let specific_contents = &mem_cs.content.as_ref().unwrap().contents;
    assert_eq!(specific_contents.len(), 1);
    assert!(specific_contents.contains_key("content_key_str"));
    assert_eq!(specific_contents["content_key_str"], original_contents_map["content_key_str"]);

    // Test Case 5: CONTENT included, empty content_fields (all content sub-fields
    // expected)
    info!("Test Case 5: CONTENT with empty content_fields");
    let search_request_content_all_sub = SearchMemoryRequest {
        query: Some(search_query_clause.clone()),
        page_size: 1,
        result_mask: Some(ResultMask {
            include_fields: vec![MemoryField::Content as i32],
            include_content_fields: vec![],
        }),
    };
    send_request_generic(tx, client_session, search_request_content_all_sub, None, mode).await;
    let (response_content_all_sub, _): (SearchMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(response_content_all_sub.results.len(), 1);
    let mem_cas = response_content_all_sub.results[0].memory.as_ref().unwrap();
    assert!(mem_cas.id.is_empty());
    assert!(mem_cas.tags.is_empty());
    assert!(mem_cas.embeddings.is_empty());
    assert!(mem_cas.content.is_some());
    assert_eq!(mem_cas.content.as_ref().unwrap().contents, original_contents_map);

    // Test Case 6: CONTENT *not* included, but content_fields specified
    info!("Test Case 6: ID included, content_fields specified (CONTENT not in include_fields)");
    let search_request_id_stray_content = SearchMemoryRequest {
        query: Some(search_query_clause.clone()),
        page_size: 1,
        result_mask: Some(ResultMask {
            include_fields: vec![MemoryField::Id as i32],
            include_content_fields: vec!["content_key_str".to_string()], // Should be ignored
        }),
    };
    send_request_generic(tx, client_session, search_request_id_stray_content, None, mode).await;
    let (response_id_stray, _): (SearchMemoryResponse, i32) =
        receive_response_generic(response_stream, client_session, mode).await;
    assert_eq!(response_id_stray.results.len(), 1);
    let mem_is = response_id_stray.results[0].memory.as_ref().unwrap();
    assert_eq!(mem_is.id, original_memory_id);
    assert!(mem_is.tags.is_empty());
    assert!(mem_is.embeddings.is_empty());
    assert!(mem_is.content.is_none());
}

async fn execute_boot_strap_logic(
    tx: &mut mpsc::Sender<SealedMemorySessionRequest>,
    client_session: &mut oak_session::ClientSession,
    response_stream: &mut tonic::Streaming<SealedMemorySessionResponse>,
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

#[tokio::test(flavor = "multi_thread")]
async fn test_add_get_reset_memory_all_modes() {
    let (addr, _db_addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{addr}");

    for &mode in [TestMode::BinaryProto, TestMode::Json].iter() {
        info!("Testing Add/Get/Reset in {:?} mode", mode);
        let channel = Channel::from_shared(url.clone()).unwrap().connect().await.unwrap();
        let mut client = SealedMemoryServiceClient::new(channel);
        let (mut tx, rx) = mpsc::channel(10);
        let mut response_stream = client.start_session(rx).await.unwrap().into_inner();
        let mut client_session = oak_session::ClientSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .unwrap();
        init_client_session_wrapped(&mut client_session, &mut tx, &mut response_stream).await;

        execute_add_get_reset_memory_logic(
            &mut tx,
            &mut client_session,
            &mut response_stream,
            mode,
        )
        .await;
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_embedding_search_all_modes() {
    let (addr, _db_addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{addr}");

    for &mode in [TestMode::BinaryProto, TestMode::Json].iter() {
        info!("Testing Embedding Search in {:?} mode", mode);
        let channel = Channel::from_shared(url.clone()).unwrap().connect().await.unwrap();
        let mut client = SealedMemoryServiceClient::new(channel);
        let (mut tx, rx) = mpsc::channel(10);
        let mut response_stream = client.start_session(rx).await.unwrap().into_inner();
        let mut client_session = oak_session::ClientSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .unwrap();

        init_client_session_wrapped(&mut client_session, &mut tx, &mut response_stream).await;

        execute_embedding_search_logic(&mut tx, &mut client_session, &mut response_stream, mode)
            .await;
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_result_masking_all_modes() {
    let (addr, _db_addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{addr}");

    for &mode in [TestMode::BinaryProto, TestMode::Json].iter() {
        info!("Testing Result Masking in {:?} mode", mode);
        let channel = Channel::from_shared(url.clone()).unwrap().connect().await.unwrap();
        let mut client = SealedMemoryServiceClient::new(channel);
        let (mut tx, rx) = mpsc::channel(10);
        let mut response_stream = client.start_session(rx).await.unwrap().into_inner();
        let mut client_session = oak_session::ClientSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .unwrap();
        init_client_session_wrapped(&mut client_session, &mut tx, &mut response_stream).await;

        execute_result_masking_logic(&mut tx, &mut client_session, &mut response_stream, mode)
            .await;
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_get_masking_all_modes() {
    let (addr, _db_addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{addr}");

    for &mode in [TestMode::BinaryProto, TestMode::Json].iter() {
        info!("Testing Get Masking in {:?} mode", mode);
        let channel = Channel::from_shared(url.clone()).unwrap().connect().await.unwrap();
        let mut client = SealedMemoryServiceClient::new(channel);
        let (mut tx, rx) = mpsc::channel(10);
        let mut response_stream = client.start_session(rx).await.unwrap().into_inner();
        let mut client_session = oak_session::ClientSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .unwrap();
        init_client_session_wrapped(&mut client_session, &mut tx, &mut response_stream).await;

        execute_get_masking_logic(&mut tx, &mut client_session, &mut response_stream, mode).await;
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_boot_strap_all_modes() {
    let (addr, _db_addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{addr}");

    for &mode in [TestMode::BinaryProto, TestMode::Json].iter() {
        info!("Testing Bootstrap in {:?} mode", mode);
        let channel = Channel::from_shared(url.clone()).unwrap().connect().await.unwrap();
        let mut client = SealedMemoryServiceClient::new(channel);
        let (mut tx, rx) = mpsc::channel(10);
        let mut response_stream = client.start_session(rx).await.unwrap().into_inner();
        let mut client_session = oak_session::ClientSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .unwrap();
        init_client_session_wrapped(&mut client_session, &mut tx, &mut response_stream).await;

        execute_boot_strap_logic(&mut tx, &mut client_session, &mut response_stream, mode).await;
    }
}

#[test]
fn proto_serialization_test() {
    init_logging();
    let request =
        KeySyncRequest { pm_uid: "12345678910".to_string(), key_encryption_key: vec![1, 2, 3] };
    info!("Serailization {:?}", serde_json::to_string(&request));
    let json_str = r#"{"keyEncryptionKey":"AQID","pmUid":"12345678910"}"#;
    let request_from_string_num = serde_json::from_str::<KeySyncRequest>(json_str).unwrap();
    assert_eq!(request.encode_to_vec(), request_from_string_num.encode_to_vec());

    let key_sync_response = KeySyncResponse { status: key_sync_response::Status::Success as i32 };
    let json_str2 = r#"{"status":"SUCCESS"}"#;
    let key_sync_response_from_string_num =
        serde_json::from_str::<KeySyncResponse>(json_str2).unwrap();
    assert_eq!(
        key_sync_response.encode_to_vec(),
        key_sync_response_from_string_num.encode_to_vec()
    );
    let json_str3 = r#"{"status": 1}"#;
    let key_sync_response_from_string_num =
        serde_json::from_str::<KeySyncResponse>(json_str3).unwrap();
    assert_eq!(
        key_sync_response.encode_to_vec(),
        key_sync_response_from_string_num.encode_to_vec()
    );

    // Test user registration response
    let user_registration_response = UserRegistrationResponse {
        status: user_registration_response::Status::UserAlreadyExists as i32,
        ..Default::default()
    };
    let json_str4 = r#"{"status":"USER_ALREADY_EXISTS"}"#;
    let user_registration_response_from_string_num =
        serde_json::from_str::<UserRegistrationResponse>(json_str4).unwrap();
    assert_eq!(
        user_registration_response.encode_to_vec(),
        user_registration_response_from_string_num.encode_to_vec()
    );

    // Test ResultMask
    let result_mask = ResultMask {
        include_fields: vec![MemoryField::Id as i32, MemoryField::Tags as i32],
        include_content_fields: vec!["content_key_str".to_string()],
    };
    let json_str5 =
        r#"{"includeFields":["ID", "TAGS"],"includeContentFields":["content_key_str"]}"#;
    let result_mask_from_string_num = serde_json::from_str::<ResultMask>(json_str5).unwrap();
    assert_eq!(result_mask.encode_to_vec(), result_mask_from_string_num.encode_to_vec());

    // Test MemoryValue with int64_val
    let memory_value = MemoryValue { value: Some(memory_value::Value::Int64Val(12345)) };
    let json_str6 = r#"{"int64Val":"12345"}"#;
    let memory_value_from_string_num = serde_json::from_str::<MemoryValue>(json_str6).unwrap();
    assert_eq!(memory_value.encode_to_vec(), memory_value_from_string_num.encode_to_vec());
}

#[tokio::test(flavor = "multi_thread")]
async fn test_delete_memory_all_modes() {
    let (addr, _db_addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{addr}");

    for &mode in [TestMode::BinaryProto, TestMode::Json].iter() {
        info!("Testing Delete Memory in {:?} mode", mode);
        let channel = Channel::from_shared(url.clone()).unwrap().connect().await.unwrap();
        let mut client = SealedMemoryServiceClient::new(channel);
        let (mut tx, rx) = mpsc::channel(10);
        let mut response_stream = client.start_session(rx).await.unwrap().into_inner();
        let mut client_session = oak_session::ClientSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .unwrap();

        init_client_session_wrapped(&mut client_session, &mut tx, &mut response_stream).await;

        execute_delete_memory_logic(&mut tx, &mut client_session, &mut response_stream, mode).await;
    }
}

async fn init_client_session_wrapped(
    client_session: &mut oak_session::ClientSession,
    tx: &mut mpsc::Sender<SealedMemorySessionRequest>,
    response_stream: &mut tonic::Streaming<SealedMemorySessionResponse>,
) {
    while !client_session.is_open() {
        let request = client_session.next_init_message().expect("failed to get next init message");
        tx.try_send(SealedMemorySessionRequest { session_request: Some(request) })
            .expect("failed to send init request");
        if !client_session.is_open() {
            let response = response_stream
                .message()
                .await
                .expect("empty init response")
                .expect("failed to get init response");
            client_session
                .handle_init_message(response.session_response.expect("missing session response"))
                .expect("failed to handle init response");
        }
    }
}
