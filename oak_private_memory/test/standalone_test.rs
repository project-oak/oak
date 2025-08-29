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

use std::{
    collections::HashMap,
    net::{IpAddr, Ipv4Addr, SocketAddr},
};

use anyhow::Result;
use client::{PrivateMemoryClient, SerializationFormat};
use log::info;
use private_memory_server_lib::{
    app::{app_service, run_persistence_service},
    app_config::ApplicationConfig,
};
use prost::Message;
use prost_types::Timestamp;
use sealed_memory_rust_proto::prelude::v1::*;
use tokio::{net::TcpListener, sync::mpsc as tokio_mpsc};

fn init_logging() {
    let _ = env_logger::builder().is_test(true).try_init();
}

static TEST_EK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";

async fn start_server() -> Result<(
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

    let metrics = private_memory_server_lib::metrics::get_global_metrics();
    let (persistence_tx, persistence_rx) = tokio_mpsc::unbounded_channel();
    let persistence_join_handle = tokio::spawn(run_persistence_service(persistence_rx));
    Ok((
        addr,
        tokio::spawn(app_service::create(listener, application_config, metrics, persistence_tx)),
        tokio::spawn(private_memory_test_database_server_lib::service::create(db_listener)),
        persistence_join_handle,
    ))
}

#[tokio::test(flavor = "multi_thread")]
async fn test_add_get_reset_memory_all_modes() {
    let (addr, _db_addr, _server_join_handle, _db_join_handle) = start_server().await.unwrap();
    let url = format!("http://{addr}");
    let pm_uid = "test_add_get_reset_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();

        let mut contents_map = HashMap::new();
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
        let memory_to_add = Memory {
            id: "".to_string(),
            content: Some(MemoryContent { contents: contents_map }),
            tags: vec!["tag".to_string()],
            ..Default::default()
        };

        let add_memory_response = client.add_memory(memory_to_add.clone()).await.unwrap();
        let memory_id_from_add = add_memory_response.id;
        client.add_memory(memory_to_add).await.unwrap();

        // GetMemoriesRequest
        let get_memories_response_1 = client.get_memories("tag", 1, None, "").await.unwrap();
        assert_eq!(get_memories_response_1.memories.len(), 1);

        let memory_content = get_memories_response_1.memories[0].content.clone().unwrap();
        assert_eq!(memory_content.contents.len(), 3);
        assert_eq!(
            memory_content.contents["text_data"].value,
            Some(memory_value::Value::BytesVal("this is a test".as_bytes().to_vec()))
        );
        assert_eq!(
            memory_content.contents["string_data"].value,
            Some(memory_value::Value::StringVal("this is a test string".to_string()))
        );
        assert_eq!(
            memory_content.contents["int64_data"].value,
            Some(memory_value::Value::Int64Val(123456789))
        );

        // GetMemoryByIdRequest
        let get_memory_by_id_response =
            client.get_memory_by_id(&memory_id_from_add, None).await.unwrap();
        assert!(get_memory_by_id_response.success);
        assert_eq!(memory_id_from_add, get_memory_by_id_response.memory.unwrap().id);

        // ResetMemoryRequest
        let reset_memory_response = client.reset_memory().await.unwrap();
        assert!(reset_memory_response.success);

        // GetMemoriesRequest again
        let get_memories_response_2 = client.get_memories("tag", 10, None, "").await.unwrap();
        assert_eq!(get_memories_response_2.memories.len(), 0);
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

    // Test Timestamp
    let timestamp = Timestamp { seconds: 1733152000, nanos: 0 };
    let memory = Memory { created_timestamp: Some(timestamp), ..Default::default() };
    let json_str7 = r#"{"createdTimestamp":"2024-12-02T15:06:40+00:00"}"#;
    let timestamp_from_string_num = serde_json::from_str::<Memory>(json_str7).unwrap();
    println!("timestamp: {:?}", timestamp);
    println!("timestamp_from_string_num: {:?}", timestamp_from_string_num);
    assert_eq!(timestamp_from_string_num.encode_to_vec(), memory.encode_to_vec());
}
