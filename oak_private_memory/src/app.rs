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

use std::collections::HashMap;

use anyhow::{bail, Context};
use oak_sdk_server_v1::ApplicationHandler;
use prost::Message;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use sealed_memory_rust_proto::oak::private_memory::{
    sealed_memory_request, sealed_memory_response, AddMemoryRequest, AddMemoryResponse,
    GetMemoriesRequest, GetMemoriesResponse, InvalidRequestResponse, KeySyncRequest,
    KeySyncResponse, Memory, ReadDataBlobRequest, ResetMemoryRequest, ResetMemoryResponse,
    SealedMemoryRequest, SealedMemoryResponse,
};
use tokio::sync::{Mutex, MutexGuard};
use tonic::transport::Channel;

use crate::app_config::ApplicationConfig;

type MemoryId = u64;
#[derive(Default)]
pub struct Database {
    inner: HashMap<MemoryId, Memory>,
}

impl Database {
    pub fn add_blob(&mut self, id: MemoryId, blob: Memory) -> bool {
        self.inner.insert(id, blob).is_none()
    }

    pub fn get_blob(&self, id: MemoryId) -> Option<Memory> {
        self.inner.get(&id).cloned()
    }
}

trait MemoryInterface {
    fn add_memory(&mut self, memory: Memory) -> Option<MemoryId>;
    fn get_memories_by_tag(&self, tag: String) -> Vec<Memory>;
    #[allow(dead_code)]
    fn reset_memory(&mut self) -> bool;
}

impl MemoryInterface for Database {
    fn add_memory(&mut self, mut memory: Memory) -> Option<MemoryId> {
        let memory_id = self.inner.len() as MemoryId;
        memory.id = memory_id.to_string();
        self.add_blob(memory_id, memory);
        Some(memory_id)
    }

    fn get_memories_by_tag(&self, tag: String) -> Vec<Memory> {
        self.inner.clone().into_values().filter(|v| v.tags.contains(&tag)).collect()
    }

    fn reset_memory(&mut self) -> bool {
        self.inner.clear();
        true
    }
}

/// The state for each client connection.
#[derive(Default)]
pub struct UserSessionContext {
    pub key: Vec<u8>,
    pub uid: u64,
    pub message_type: MessageType,

    pub database: Database,
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
    pub application_config: ApplicationConfig,
    pub session_context: Mutex<Option<UserSessionContext>>,
    pub database_service_client: Mutex<SealedMemoryDatabaseServiceClient<Channel>>,
}

impl SealedMemoryHandler {
    pub async fn new(application_config_bytes: &[u8]) -> Self {
        let application_config: ApplicationConfig =
            serde_json::from_slice(application_config_bytes).expect("Invalid application config");
        let db_addr = application_config.database_service_host;
        let db_url = format!("http://{db_addr}");
        let db_channel = Channel::from_shared(db_url)
            .context("couldn't create database channel")
            .unwrap()
            .connect()
            .await
            .context("couldn't connect via database channel")
            .unwrap();

        let db_client = SealedMemoryDatabaseServiceClient::new(db_channel);

        Self {
            application_config,
            session_context: Default::default(),
            database_service_client: Mutex::new(db_client),
        }
    }
}

impl SealedMemoryHandler {
    pub fn session_context_established(&self) -> bool {
        self.session_context.blocking_lock().is_some()
    }

    pub async fn session_context(&self) -> MutexGuard<'_, Option<UserSessionContext>> {
        self.session_context.lock().await
    }

    pub fn deserialize_request(&self, request_bytes: &[u8]) -> Option<SealedMemoryRequest> {
        SealedMemoryRequest::decode(request_bytes).ok()
    }

    pub fn is_binary_proto_request(&self, request_bytes: &[u8]) -> bool {
        self.deserialize_request(request_bytes).is_some()
    }

    pub fn serialize_response(&self, response: &SealedMemoryResponse) -> Vec<u8> {
        response.encode_to_vec()
    }

    // Memory related handlers

    pub async fn add_memory_handler(
        &self,
        request: AddMemoryRequest,
    ) -> anyhow::Result<AddMemoryResponse> {
        let mut mutex_guard = self.session_context().await;
        let context: &mut Option<UserSessionContext> = &mut mutex_guard;
        if let Some(context) = context {
            let database = &mut context.database;
            let memory_id = database.add_memory(request.memory.unwrap()).unwrap();
            Ok(AddMemoryResponse { id: memory_id.to_string() })
        } else {
            bail!("This is an error")
        }
    }

    pub async fn get_memories_handler(
        &self,
        request: GetMemoriesRequest,
    ) -> anyhow::Result<GetMemoriesResponse> {
        let mut mutex_guard = self.session_context().await;
        let context: &mut Option<UserSessionContext> = &mut mutex_guard;
        if let Some(context) = context {
            let database = &mut context.database;
            let memories = database.get_memories_by_tag(request.tag);
            Ok(GetMemoriesResponse { memories })
        } else {
            bail!("This is an error")
        }
    }

    pub fn reset_memory_handler(
        &self,
        _request: ResetMemoryRequest,
    ) -> anyhow::Result<ResetMemoryResponse> {
        Ok(ResetMemoryResponse::default())
    }

    pub async fn key_sync_handler(
        &self,
        _request: KeySyncRequest,
    ) -> anyhow::Result<KeySyncResponse> {
        let mut mutex_guard = self.session_context().await;
        if mutex_guard.is_some() {
            bail!("already setup the session");
        }
        *mutex_guard = Some(UserSessionContext::default());

        Ok(KeySyncResponse::default())
    }
}

pub trait RequestUnpacking {
    fn from_request(x: SealedMemoryRequest) -> Option<Self>
    where
        Self: Sized;
    fn into_request(self) -> SealedMemoryRequest;
}
pub trait ResponsePacking {
    fn into_response(self) -> SealedMemoryResponse;
    fn from_response(x: SealedMemoryResponse) -> Option<Self>
    where
        Self: Sized;
}

impl RequestUnpacking for KeySyncRequest {
    fn from_request(x: SealedMemoryRequest) -> Option<Self> {
        match x.request {
            Some(sealed_memory_request::Request::KeySyncRequest(request)) => Some(request),
            _ => None,
        }
    }

    fn into_request(self) -> SealedMemoryRequest {
        SealedMemoryRequest { request: Some(sealed_memory_request::Request::KeySyncRequest(self)) }
    }
}

impl RequestUnpacking for AddMemoryRequest {
    fn from_request(x: SealedMemoryRequest) -> Option<Self> {
        match x.request {
            Some(sealed_memory_request::Request::AddMemoryRequest(request)) => Some(request),
            _ => None,
        }
    }

    fn into_request(self) -> SealedMemoryRequest {
        SealedMemoryRequest {
            request: Some(sealed_memory_request::Request::AddMemoryRequest(self)),
        }
    }
}

impl RequestUnpacking for GetMemoriesRequest {
    fn from_request(x: SealedMemoryRequest) -> Option<Self> {
        match x.request {
            Some(sealed_memory_request::Request::GetMemoriesRequest(request)) => Some(request),
            _ => None,
        }
    }

    fn into_request(self) -> SealedMemoryRequest {
        SealedMemoryRequest {
            request: Some(sealed_memory_request::Request::GetMemoriesRequest(self)),
        }
    }
}

impl ResponsePacking for KeySyncResponse {
    fn into_response(self) -> SealedMemoryResponse {
        SealedMemoryResponse {
            response: Some(sealed_memory_response::Response::KeySyncResponse(self)),
        }
    }
    fn from_response(x: SealedMemoryResponse) -> Option<Self> {
        match x.response {
            Some(sealed_memory_response::Response::KeySyncResponse(response)) => Some(response),
            _ => None,
        }
    }
}

impl ResponsePacking for AddMemoryResponse {
    fn into_response(self) -> SealedMemoryResponse {
        SealedMemoryResponse {
            response: Some(sealed_memory_response::Response::AddMemoryResponse(self)),
        }
    }

    fn from_response(x: SealedMemoryResponse) -> Option<Self> {
        match x.response {
            Some(sealed_memory_response::Response::AddMemoryResponse(response)) => Some(response),
            _ => None,
        }
    }
}

impl ResponsePacking for GetMemoriesResponse {
    fn into_response(self) -> SealedMemoryResponse {
        SealedMemoryResponse {
            response: Some(sealed_memory_response::Response::GetMemoriesResponse(self)),
        }
    }
    fn from_response(x: SealedMemoryResponse) -> Option<Self> {
        match x.response {
            Some(sealed_memory_response::Response::GetMemoriesResponse(response)) => Some(response),
            _ => None,
        }
    }
}

impl ResponsePacking for InvalidRequestResponse {
    fn into_response(self) -> SealedMemoryResponse {
        SealedMemoryResponse {
            response: Some(sealed_memory_response::Response::InvalidRequestResponse(self)),
        }
    }
    fn from_response(x: SealedMemoryResponse) -> Option<Self> {
        match x.response {
            Some(sealed_memory_response::Response::InvalidRequestResponse(response)) => {
                Some(response)
            }
            _ => None,
        }
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
            let response: SealedMemoryResponse = InvalidRequestResponse {
                error_message: "Invalid json or binary proto format".into(),
            }
            .into_response();
            return Ok(self.serialize_response(&response));
        }

        // For test purpose. Will be removed soon
        let db_request = ReadDataBlobRequest::default();
        let db_response = self
            .database_service_client
            .lock()
            .await
            .read_data_blob(db_request)
            .await
            .expect("Received response")
            .into_inner();
        println!("db response {:#?}", db_response);

        let request = request.unwrap().request.expect("The request should not empty!");
        let response = match request {
            sealed_memory_request::Request::KeySyncRequest(request) => {
                self.key_sync_handler(request).await?.into_response()
            }
            sealed_memory_request::Request::AddMemoryRequest(request) => {
                self.add_memory_handler(request).await?.into_response()
            }
            sealed_memory_request::Request::GetMemoriesRequest(request) => {
                self.get_memories_handler(request).await?.into_response()
            }
            _ => InvalidRequestResponse { error_message: "Unhandled request types".into() }
                .into_response(),
        };

        Ok(self.serialize_response(&response))
    }
}
