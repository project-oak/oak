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

use anyhow::{bail, Context};
use async_trait::async_trait;
use oak_sdk_server_v1::ApplicationHandler;
use prost::Message;
use rand::Rng;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use sealed_memory_rust_proto::oak::private_memory::{
    sealed_memory_request, sealed_memory_response, AddMemoryRequest, AddMemoryResponse,
    GetMemoriesRequest, GetMemoriesResponse, GetMemoryByIdRequest, GetMemoryByIdResponse,
    InvalidRequestResponse, KeySyncRequest, KeySyncResponse, Memory, ResetMemoryRequest,
    ResetMemoryResponse, SealedMemoryRequest, SealedMemoryResponse,
};
use tokio::{
    runtime::Handle,
    sync::{Mutex, MutexGuard},
};
use tonic::transport::Channel;

use crate::{
    app_config::ApplicationConfig,
    database::{
        decrypt_database, encrypt_database, BlobId, DataBlobHandler, DatabaseWithCache, MemoryId,
        MetaDatabase,
    },
    debug,
};

#[async_trait]
trait MemoryInterface {
    async fn add_memory(&mut self, memory: Memory) -> Option<MemoryId>;
    async fn get_memories_by_tag(&mut self, tag: String) -> Vec<Memory>;
    async fn get_memory_by_id(&mut self, id: MemoryId) -> Option<Memory>;
    async fn reset_memory(&mut self) -> bool;
}

#[async_trait]
impl MemoryInterface for DatabaseWithCache {
    async fn add_memory(&mut self, mut memory: Memory) -> Option<MemoryId> {
        let memory_id = if memory.id.is_empty() {
            let id = rand::rng().random::<u64>().to_string();
            memory.id = id.clone();
            id
        } else {
            memory.id.clone()
        };
        let blob_id = self.cache.add_memory(memory).await.ok()?;
        self.meta_db().add_memory(memory_id.clone(), blob_id);
        Some(memory_id)
    }

    async fn get_memories_by_tag(&mut self, tag: String) -> Vec<Memory> {
        let all_blob_ids: Vec<BlobId> = self.meta_db().all_blob_ids();

        if all_blob_ids.is_empty() {
            return Vec::new();
        }

        // 2. Fetch all memories using the cache
        match self.cache.get_memories_by_blob_ids(&all_blob_ids).await {
            Ok(all_memories) => {
                // 3. Filter by tag
                all_memories.into_iter().filter(|m| m.tags.contains(&tag)).collect()
            }
            Err(e) => {
                log::error!("Failed to fetch memories by blob IDs: {:?}", e);
                Vec::new() // Return empty vec on error
            }
        }
    }

    async fn get_memory_by_id(&mut self, id: MemoryId) -> Option<Memory> {
        if let Some(blob_id) = self.meta_db().get_blob_id_by_memory_id(id) {
            self.cache.get_memory_by_blob_id(&blob_id).await.ok()
        } else {
            None
        }
    }

    async fn reset_memory(&mut self) -> bool {
        self.meta_db().reset();
        true
    }
}

/// The state for each client connection.
pub struct UserSessionContext {
    pub key: Vec<u8>,
    pub uid: i64,
    pub message_type: MessageType,

    pub database: DatabaseWithCache,
    pub database_service_client: SealedMemoryDatabaseServiceClient<Channel>,
}

// The message format for the plaintext.
#[derive(Default, Copy, Clone)]
pub enum MessageType {
    #[default]
    BinaryProto,
    Json,
}

/// The actual business logic for the hello world application.
pub struct SealedMemoryHandler {
    pub application_config: ApplicationConfig,
    pub session_context: Mutex<Option<UserSessionContext>>,
}

impl Drop for SealedMemoryHandler {
    fn drop(&mut self) {
        debug!("Dropping");
        let session_context = std::mem::take(&mut self.session_context);
        // When this is called, we should perform cleanup routines like persisting
        // the in memory database to disks.
        Handle::current().spawn(async move {
            debug!("Enter");
            // For test purpose. Will be removed soon
            if let Some(user_context) = session_context.lock().await.as_mut() {
                let database =
                    encrypt_database(&user_context.database.meta_db(), &user_context.key);
                if database.is_err() {
                    debug!("Failed to serialize database");
                    return;
                }
                let database = database.unwrap();
                debug!("Saving db size: {}", database.data.len());
                debug!("Saving nonce: {}", database.nonce.len());
                let result = user_context
                    .database_service_client
                    .add_blob(database, Some(user_context.uid))
                    .await;
                debug!("db response {:#?}", result);
            }
        });
    }
}

impl Clone for SealedMemoryHandler {
    fn clone(&self) -> Self {
        Self {
            application_config: self.application_config.clone(),
            session_context: Default::default(),
        }
    }
}

impl SealedMemoryHandler {
    pub async fn new(application_config_bytes: &[u8]) -> Self {
        let application_config: ApplicationConfig =
            serde_json::from_slice(application_config_bytes).expect("Invalid application config");

        Self { application_config, session_context: Default::default() }
    }
}

impl SealedMemoryHandler {
    pub async fn session_context_established(&self) -> bool {
        self.session_context().await.is_some()
    }

    pub async fn session_context(&self) -> MutexGuard<'_, Option<UserSessionContext>> {
        self.session_context.lock().await
    }

    pub async fn get_message_type(&self) -> MessageType {
        self.session_context().await.as_mut().unwrap().message_type
    }

    pub fn is_message_type_json(&self, request_bytes: &[u8]) -> bool {
        serde_json::from_slice::<SealedMemoryRequest>(request_bytes).is_ok()
    }

    pub async fn deserialize_request(&self, request_bytes: &[u8]) -> Option<SealedMemoryRequest> {
        if self.session_context_established().await {
            match self.get_message_type().await {
                MessageType::BinaryProto => SealedMemoryRequest::decode(request_bytes).ok(),
                MessageType::Json => {
                    serde_json::from_slice::<SealedMemoryRequest>(request_bytes).ok()
                }
            }
        } else if let Ok(request) = SealedMemoryRequest::decode(request_bytes) {
            debug!("Request is in binary proto format");
            Some(request)
        } else if let Ok(request) = serde_json::from_slice::<SealedMemoryRequest>(request_bytes) {
            debug!("Request is in json format {:?}", request);
            Some(request)
        } else {
            None
        }
    }

    pub async fn serialize_response(&self, response: &SealedMemoryResponse) -> Vec<u8> {
        if self.session_context_established().await {
            match self.get_message_type().await {
                MessageType::BinaryProto => {
                    return response.encode_to_vec();
                }
                MessageType::Json => {
                    return serde_json::to_vec(response).unwrap();
                }
            }
        }
        // Default to binary proto if the session is not established.
        response.encode_to_vec()
    }

    fn is_valid_key(key: &[u8]) -> bool {
        // Only support 256-bit key for now.
        key.len() == 32
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
            let memory_id = database.add_memory(request.memory.unwrap()).await;
            if let Some(memory_id) = memory_id {
                Ok(AddMemoryResponse { id: memory_id.to_string() })
            } else {
                bail!("Failed to add memory!")
            }
        } else {
            bail!("You need to call key sync first")
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
            let memories = database.get_memories_by_tag(request.tag).await;
            Ok(GetMemoriesResponse { memories })
        } else {
            bail!("You need to call key sync first")
        }
    }

    pub async fn get_memory_by_id_handler(
        &self,
        request: GetMemoryByIdRequest,
    ) -> anyhow::Result<GetMemoryByIdResponse> {
        let mut mutex_guard = self.session_context().await;
        let context: &mut Option<UserSessionContext> = &mut mutex_guard;
        if let Some(context) = context {
            let database = &mut context.database;
            let memory = database.get_memory_by_id(request.id).await;
            let success = memory.is_some();
            Ok(GetMemoryByIdResponse { memory, success })
        } else {
            bail!("You need to call key sync first")
        }
    }

    pub async fn reset_memory_handler(
        &self,
        _request: ResetMemoryRequest,
    ) -> anyhow::Result<ResetMemoryResponse> {
        let mut mutex_guard = self.session_context().await;
        let context: &mut Option<UserSessionContext> = &mut mutex_guard;
        if let Some(context) = context {
            let database = &mut context.database;
            database.reset_memory().await;
            Ok(ResetMemoryResponse { success: true, ..Default::default() })
        } else {
            bail!("You need to call key sync first")
        }
    }

    pub async fn key_sync_handler(
        &self,
        request: KeySyncRequest,
        is_json: bool,
    ) -> anyhow::Result<KeySyncResponse> {
        const INVALID_UID: i64 = 0;
        if request.data_encryption_key.is_empty() || request.uid == INVALID_UID {
            bail!("uid or key not set in request");
        }
        let key = request.data_encryption_key;
        let uid = request.uid;
        if !Self::is_valid_key(&key) {
            bail!("Not a valid key!");
        }

        let db_addr = self.application_config.database_service_host;
        let db_url = format!("http://{db_addr}");
        log::debug!("Database addr {}", db_url);
        let db_channel = Channel::from_shared(db_url)
            .context("couldn't create database channel")
            .unwrap()
            .connect()
            .await
            .context("couldn't connect via database channel")
            .unwrap();

        let mut db_client = SealedMemoryDatabaseServiceClient::new(db_channel);
        debug!("Trying to get datablob");
        let database = if let Ok(data_blob) = db_client.get_blob(&uid).await {
            let database = decrypt_database(data_blob, &key)?;
            debug!("Loaded database successfully!!");
            database
        } else {
            MetaDatabase::default()
        };
        let mut mutex_guard = self.session_context().await;
        if mutex_guard.is_some() {
            bail!("already setup the session");
        }
        let message_type = if is_json { MessageType::Json } else { MessageType::BinaryProto };
        *mutex_guard = Some(UserSessionContext {
            key: key.clone(),
            uid,
            message_type,
            database_service_client: db_client.clone(),
            database: DatabaseWithCache::new(database, key, db_client),
        });

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

macro_rules! impl_packing {
    (Request => $name:ident) => {
        impl RequestUnpacking for $name {
            fn from_request(x: SealedMemoryRequest) -> Option<Self> {
                match x.request {
                    Some(sealed_memory_request::Request::$name(request)) => Some(request),
                    _ => None,
                }
            }

            fn into_request(self) -> SealedMemoryRequest {
                SealedMemoryRequest {
                    request: Some(sealed_memory_request::Request::$name(self)),
                    request_id: 0,
                }
            }
        }
    };

    (Response => $name:ident) => {
        impl ResponsePacking for $name {
            fn from_response(x: SealedMemoryResponse) -> Option<Self> {
                match x.response {
                    Some(sealed_memory_response::Response::$name(response)) => Some(response),
                    _ => None,
                }
            }

            fn into_response(self) -> SealedMemoryResponse {
                SealedMemoryResponse {
                    response: Some(sealed_memory_response::Response::$name(self)),
                    request_id: 0,
                }
            }
        }
    };
}
impl_packing!(Request => AddMemoryRequest);
impl_packing!(Request => GetMemoriesRequest);
impl_packing!(Request => ResetMemoryRequest);
impl_packing!(Request => KeySyncRequest);
impl_packing!(Request => GetMemoryByIdRequest);
impl_packing!(Response => AddMemoryResponse);
impl_packing!(Response => GetMemoriesResponse);
impl_packing!(Response => ResetMemoryResponse);
impl_packing!(Response => InvalidRequestResponse);
impl_packing!(Response => KeySyncResponse);
impl_packing!(Response => GetMemoryByIdResponse);

#[async_trait::async_trait]
impl ApplicationHandler for SealedMemoryHandler {
    /// This implementation is quite simple, since there's just a single request
    /// that is a string. In a real implementation, we'd probably
    /// deserialize into a proto, and dispatch to various handlers from
    /// there.
    async fn handle(&self, request_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        let request = self.deserialize_request(request_bytes).await;
        let response = if request.is_none() {
            InvalidRequestResponse { error_message: "Invalid json or binary proto format".into() }
                .into_response()
        } else {
            let request = request.unwrap();
            let request_id = request.request_id;
            let request = request.request;
            if request.is_none() {
                bail!("The request is empty. The json format might be incorrect: the data type should strictly match.");
            }
            let request = request.unwrap();
            let mut response = match request {
                sealed_memory_request::Request::KeySyncRequest(request) => self
                    .key_sync_handler(request, self.is_message_type_json(request_bytes))
                    .await?
                    .into_response(),
                sealed_memory_request::Request::AddMemoryRequest(request) => {
                    self.add_memory_handler(request).await?.into_response()
                }
                sealed_memory_request::Request::GetMemoriesRequest(request) => {
                    self.get_memories_handler(request).await?.into_response()
                }
                sealed_memory_request::Request::ResetMemoryRequest(request) => {
                    self.reset_memory_handler(request).await?.into_response()
                }
                sealed_memory_request::Request::GetMemoryByIdRequest(request) => {
                    self.get_memory_by_id_handler(request).await?.into_response()
                }
            };
            response.request_id = request_id;
            response
        };

        Ok(self.serialize_response(&response).await)
    }
}
