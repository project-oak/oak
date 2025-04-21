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
    sealed_memory_request, sealed_memory_response, AddMemoryRequest, AddMemoryResponse, DataBlob,
    GetMemoriesRequest, GetMemoriesResponse, GetMemoryByIdRequest, GetMemoryByIdResponse,
    InvalidRequestResponse, KeySyncRequest, KeySyncResponse, Memory, ReadDataBlobRequest,
    ResetMemoryRequest, ResetMemoryResponse, SealedMemoryRequest, SealedMemoryResponse,
    WriteDataBlobRequest,
};
use tokio::{
    runtime::Handle,
    sync::{Mutex, MutexGuard},
};
use tonic::transport::Channel;

use crate::{
    app_config::ApplicationConfig,
    debug,
    encryption::{decrypt, encrypt, generate_nonce},
};

type MemoryId = String;
#[derive(Default, serde::Serialize, serde::Deserialize)]
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

    pub fn reset(&mut self) {
        self.inner.clear();
    }
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct EncryptedDatablob {
    pub nonce: Vec<u8>,
    pub data: Vec<u8>,
}

fn encrypt_database(database: &Database, key: &[u8]) -> anyhow::Result<EncryptedDatablob> {
    let nonce = generate_nonce();
    let datablob = serde_json::to_vec(database)?;
    let data = encrypt(key, &nonce, &datablob)?;
    Ok(EncryptedDatablob { nonce, data })
}

fn decrypt_database(datablob: EncryptedDatablob, key: &[u8]) -> anyhow::Result<Database> {
    let nonce = datablob.nonce;
    let data = datablob.data;
    let decrypted_data = decrypt(key, &nonce, &data)?;
    Ok(serde_json::from_slice::<Database>(&decrypted_data)?)
}

trait MemoryInterface {
    fn add_memory(&mut self, memory: Memory) -> Option<MemoryId>;
    fn get_memories_by_tag(&self, tag: String) -> Vec<Memory>;
    fn get_memory_by_id(&self, id: MemoryId) -> Option<Memory>;
    #[allow(dead_code)]
    fn reset_memory(&mut self) -> bool;
}

impl MemoryInterface for Database {
    fn add_memory(&mut self, mut memory: Memory) -> Option<MemoryId> {
        let memory_id = if memory.id.is_empty() {
            let id = self.inner.len().to_string();
            memory.id = id.clone();
            id
        } else {
            memory.id.clone()
        };
        self.add_blob(memory_id.clone(), memory);
        Some(memory_id)
    }

    fn get_memories_by_tag(&self, tag: String) -> Vec<Memory> {
        self.inner.clone().into_values().filter(|v| v.tags.contains(&tag)).collect()
    }

    fn get_memory_by_id(&self, id: MemoryId) -> Option<Memory> {
        self.get_blob(id)
    }

    fn reset_memory(&mut self) -> bool {
        self.inner.clear();
        true
    }
}

/// The state for each client connection.
pub struct UserSessionContext {
    pub key: Vec<u8>,
    pub uid: i64,
    pub message_type: MessageType,

    pub database: Database,
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
                let database = encrypt_database(&user_context.database, &user_context.key);
                if database.is_err() {
                    debug!("Failed to serialize database");
                    return;
                }
                let encrypted_datablob = serde_json::to_vec(&database.unwrap());
                if encrypted_datablob.is_err() {
                    debug!("Failed to serialize database");
                    return;
                }
                let encrypted_datablob = encrypted_datablob.unwrap();
                let data_blob =
                    DataBlob { id: user_context.uid, encrypted_blob: encrypted_datablob };
                let db_response = user_context
                    .database_service_client
                    .write_data_blob(WriteDataBlobRequest { data_blob: Some(data_blob) })
                    .await
                    .expect("Received response")
                    .into_inner();
                debug!("db response {:#?}", db_response);
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
            let memory_id = database.add_memory(request.memory.unwrap()).unwrap();
            Ok(AddMemoryResponse { id: memory_id.to_string() })
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
            let memories = database.get_memories_by_tag(request.tag);
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
            let memory = database.get_memory_by_id(request.id);
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
            database.reset();
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
        let db_response = db_client
            .read_data_blob(ReadDataBlobRequest { id: uid })
            .await
            .expect("Load database failed!")
            .into_inner();
        let database = if let Some(status) = db_response.status {
            if status.success && db_response.data_blob.is_some() {
                let data_blob = db_response.data_blob.unwrap();
                let encrypted_datablob =
                    serde_json::from_slice::<EncryptedDatablob>(&data_blob.encrypted_blob)?;
                let database = decrypt_database(encrypted_datablob, &key)?;
                debug!("Loaded database successfully {}!!", serde_json::to_string(&database)?);
                database
            } else {
                debug!("Failed to load database");
                Database::default()
            }
        } else {
            debug!("Failed to load database");
            Database::default()
        };
        let mut mutex_guard = self.session_context().await;
        if mutex_guard.is_some() {
            bail!("already setup the session");
        }
        let message_type = if is_json { MessageType::Json } else { MessageType::BinaryProto };
        *mutex_guard = Some(UserSessionContext {
            key,
            uid,
            message_type,
            database_service_client: db_client,
            database,
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
