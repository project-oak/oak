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

use log::info;
use prost::Message;
use prost_types::Timestamp;
use sealed_memory_rust_proto::prelude::v1::*;

fn init_logging() {
    let _ = env_logger::builder().is_test(true).try_init();
}

#[test]
fn test_key_sync_request_serialization() {
    init_logging();
    let request =
        KeySyncRequest { pm_uid: "12345678910".to_string(), key_encryption_key: vec![1, 2, 3] };
    info!("Serailization {:?}", serde_json::to_string(&request));
    let json_str = r#"{"keyEncryptionKey":"AQID","pmUid":"12345678910"}"#;
    let request_from_string_num = serde_json::from_str::<KeySyncRequest>(json_str).unwrap();
    assert_eq!(request.encode_to_vec(), request_from_string_num.encode_to_vec());
}

#[test]
fn test_key_sync_response_serialization() {
    init_logging();
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
}

#[test]
fn test_user_registration_response_serialization() {
    init_logging();
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
}

#[test]
fn test_result_mask_serialization() {
    init_logging();
    let result_mask = ResultMask {
        include_fields: vec![MemoryField::Id as i32, MemoryField::Tags as i32],
        include_content_fields: vec!["content_key_str".to_string()],
    };
    let json_str5 =
        r#"{"includeFields":["ID", "TAGS"],"includeContentFields":["content_key_str"]}"#;
    let result_mask_from_string_num = serde_json::from_str::<ResultMask>(json_str5).unwrap();
    assert_eq!(result_mask.encode_to_vec(), result_mask_from_string_num.encode_to_vec());
}

#[test]
fn test_memory_value_serialization() {
    init_logging();
    let memory_value = MemoryValue { value: Some(memory_value::Value::Int64Val(12345)) };
    let json_str6 = r#"{"int64Val":"12345"}"#;
    let memory_value_from_string_num = serde_json::from_str::<MemoryValue>(json_str6).unwrap();
    assert_eq!(memory_value.encode_to_vec(), memory_value_from_string_num.encode_to_vec());
}

#[test]
fn test_memory_with_timestamp_serialization() {
    init_logging();
    let timestamp = Timestamp { seconds: 1733152000, nanos: 0 };
    let memory = Memory { created_timestamp: Some(timestamp), ..Default::default() };
    let json_str7 = r#"{"createdTimestamp":"2024-12-02T15:06:40+00:00"}"#;
    let timestamp_from_string_num = serde_json::from_str::<Memory>(json_str7).unwrap();
    println!("timestamp: {:?}", timestamp);
    println!("timestamp_from_string_num: {:?}", timestamp_from_string_num);
    assert_eq!(timestamp_from_string_num.encode_to_vec(), memory.encode_to_vec());
}
