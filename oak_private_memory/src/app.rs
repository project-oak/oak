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

use oak_sdk_server_v1::ApplicationHandler;
use prost::Message;
use sealed_memory_rust_proto::oak::private_memory::{
    sealed_memory_request, sealed_memory_response, AddMemoryRequest, AddMemoryResponse,
    GetMemoriesRequest, GetMemoriesResponse, InvalidRequestResponse, KeySyncRequest,
    KeySyncResponse, ResetMemoryRequest, ResetMemoryResponse, SealedMemoryRequest,
    SealedMemoryResponse,
};
use tokio::sync::{Mutex, MutexGuard};

/// The state for each client connection.
#[derive(Default)]
pub struct UserSessionContext {
    pub key: Vec<u8>,
    pub uid: u64,
    pub message_type: MessageType,
}

// The message format for the plaintext.
#[derive(Default)]
pub enum MessageType {
    #[default]
    BinaryProto,
    Json,
}

/// The actual business logic for the hello world application.
pub struct SealedMemoryHandler {
    pub application_config: Vec<u8>,
    pub session_context: Mutex<Option<UserSessionContext>>,
}

impl SealedMemoryHandler {
    pub fn session_context_established(&self) -> bool {
        self.session_context.blocking_lock().is_some()
    }

    pub fn session_context(&mut self) -> MutexGuard<'_, Option<UserSessionContext>> {
        self.session_context.blocking_lock()
    }

    pub fn deserialize_request(&self, request_bytes: &[u8]) -> Option<SealedMemoryRequest> {
        SealedMemoryRequest::decode(request_bytes).ok()
    }

    pub fn serialize_response(&self, response: &SealedMemoryResponse) -> Vec<u8> {
        response.encode_to_vec()
    }

    // Memory related handlers

    pub fn add_memory_handler(
        &self,
        _request: AddMemoryRequest,
    ) -> anyhow::Result<AddMemoryResponse> {
        Ok(AddMemoryResponse::default())
    }

    pub fn get_memories_handler(
        &self,
        _request: GetMemoriesRequest,
    ) -> anyhow::Result<GetMemoriesResponse> {
        Ok(GetMemoriesResponse::default())
    }

    pub fn reset_memory_handler(
        &self,
        _request: ResetMemoryRequest,
    ) -> anyhow::Result<ResetMemoryResponse> {
        Ok(ResetMemoryResponse::default())
    }

    pub fn key_sync_handler(&self, _request: KeySyncRequest) -> anyhow::Result<KeySyncResponse> {
        Ok(KeySyncResponse::default())
    }
}

#[async_trait::async_trait]
impl ApplicationHandler for SealedMemoryHandler {
    /// This implementation is quite simple, since there's just a single request
    /// that is a string. In a real implementation, we'd probably
    /// deserialize into a proto, and dispatch to various handlers from
    /// there.
    async fn handle(&self, request_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        let request = self.deserialize_request(request_bytes);
        if request.is_none() {
            let response = SealedMemoryResponse {
                response: Some(sealed_memory_response::Response::InvalidRequestResponse(
                    InvalidRequestResponse {
                        error_message: "Invalid json or binary proto format".into(),
                    },
                )),
            };
            return Ok(self.serialize_response(&response));
        }

        let request = request.unwrap().request.unwrap();
        match request {
            sealed_memory_request::Request::AddMemoryRequest(_) => {
                println!("this is a add requset");
            }
            sealed_memory_request::Request::GetMemoriesRequest(_) => {
                println!("this is a get requset");
            }
            _ => {}
        }

        Ok("".into())
    }
}
