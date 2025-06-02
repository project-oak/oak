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
    key_sync_response, sealed_memory_request, sealed_memory_response, user_registration_response,
    AddMemoryRequest, AddMemoryResponse, DataBlob, Embedding, EncryptedDataBlob, EncryptedUserInfo,
    GetMemoriesRequest, GetMemoriesResponse, GetMemoryByIdRequest, GetMemoryByIdResponse,
    InvalidRequestResponse, KeySyncRequest, KeySyncResponse, Memory, PlainTextUserInfo,
    ResetMemoryRequest, ResetMemoryResponse, ScoreRange, SealedMemoryRequest, SealedMemoryResponse,
    SearchMemoryRequest, SearchMemoryResponse, SearchMemoryResultItem, UserRegistrationRequest,
    UserRegistrationResponse, WrappedDataEncryptionKey,
};
use tokio::{
    runtime::Handle,
    sync::{Mutex, MutexGuard},
};
use tonic::transport::Channel;

use crate::{
    app_config::ApplicationConfig,
    database::{
        decrypt_database, encrypt_database, BlobId, DataBlobHandler, DatabaseWithCache,
        DbMigration, IcingMetaDatabase, MemoryId,
    },
    debug,
    encryption::{decrypt, encrypt, generate_nonce},
};

#[async_trait]
trait MemoryInterface {
    async fn add_memory(&mut self, memory: Memory) -> Option<MemoryId>;
    async fn get_memories_by_tag(&mut self, tag: String) -> Vec<Memory>;
    async fn get_memory_by_id(&mut self, id: MemoryId) -> Option<Memory>;
    async fn reset_memory(&mut self) -> bool;
    async fn search_memory(
        &mut self,
        query: &[Embedding],
        limit: u32,
        score_range: Option<ScoreRange>,
    ) -> Vec<SearchMemoryResultItem>;
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
        let blob_id = self.cache.add_memory(memory.clone()).await.ok()?;
        let _ = self.meta_db().add_memory(memory, blob_id);
        Some(memory_id)
    }

    async fn get_memories_by_tag(&mut self, tag: String) -> Vec<Memory> {
        let all_blob_ids: Vec<BlobId> = self.meta_db().get_memories_by_tag(tag).unwrap();

        if all_blob_ids.is_empty() {
            return Vec::new();
        }

        self.cache.get_memories_by_blob_ids(&all_blob_ids).await.unwrap()
    }

    async fn get_memory_by_id(&mut self, id: MemoryId) -> Option<Memory> {
        if let Some(blob_id) = self.meta_db().get_blob_id_by_memory_id(id).unwrap() {
            self.cache.get_memory_by_blob_id(&blob_id).await.ok()
        } else {
            None
        }
    }

    async fn reset_memory(&mut self) -> bool {
        self.meta_db().reset();
        true
    }

    async fn search_memory(
        &mut self,
        query: &[Embedding],
        limit: u32,
        score_range: Option<ScoreRange>,
    ) -> Vec<SearchMemoryResultItem> {
        let (blob_ids, scores) =
            self.meta_db().embedding_search(query, limit, score_range).unwrap();
        let memories = self.cache.get_memories_by_blob_ids(&blob_ids).await.unwrap();
        memories
            .into_iter()
            .zip(scores.into_iter())
            .map(|(memory, _score)| SearchMemoryResultItem { memory: Some(memory) })
            .collect()
    }
}

/// The state for each client connection.
pub struct UserSessionContext {
    pub dek: Vec<u8>,
    pub uid: String,
    pub message_type: MessageType,

    pub database: DatabaseWithCache,
    pub database_service_client: SealedMemoryDatabaseServiceClient<Channel>,
}

// The message format for the plaintext.
#[derive(Default, Copy, Clone, PartialEq)]
pub enum MessageType {
    #[default]
    BinaryProto,
    Json,
}

/// The actual business logic for the hello world application.
pub struct SealedMemoryHandler {
    pub application_config: ApplicationConfig,
    pub session_context: Mutex<Option<UserSessionContext>>,
    db_client_cache: Mutex<Option<SealedMemoryDatabaseServiceClient<Channel>>>,
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
                let database = encrypt_database(
                    &user_context.database.export().encrypted_info.unwrap(),
                    &user_context.dek,
                );
                if database.is_err() {
                    debug!("Failed to serialize database");
                    return;
                }
                let database = database.unwrap();
                debug!("Saving db size: {}", database.data.len());
                debug!("Saving nonce: {}", database.nonce.len());
                let result = user_context
                    .database_service_client
                    .add_blob(database, Some(user_context.uid.clone()))
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
            db_client_cache: Default::default(),
        }
    }
}

impl SealedMemoryHandler {
    pub async fn new(application_config_bytes: &[u8]) -> Self {
        let application_config: ApplicationConfig =
            serde_json::from_slice(application_config_bytes).expect("Invalid application config");

        Self {
            application_config,
            session_context: Default::default(),
            db_client_cache: Mutex::new(None),
        }
    }

    pub async fn session_context_established(&self) -> bool {
        self.session_context().await.is_some()
    }

    pub async fn session_context(&self) -> MutexGuard<'_, Option<UserSessionContext>> {
        self.session_context.lock().await
    }

    /// Returns a database service client.
    ///
    /// If a client has been established for this handler instance, a clone of
    /// it is returned. Otherwise, a new client is established, cached for
    /// future use by this handler instance, and then returned.
    pub async fn get_db_client(
        &self,
    ) -> anyhow::Result<SealedMemoryDatabaseServiceClient<Channel>> {
        let mut guard = self.db_client_cache.lock().await;
        if let Some(client) = guard.as_ref() {
            debug!("Reusing cached DB client");
            return Ok(client.clone());
        }

        debug!("Creating new DB client");
        let db_addr = self.application_config.database_service_host;
        // The format "http://<host>:<port>" is expected by tonic.
        let db_url = format!("http://{db_addr}");
        debug!("Database service URL: {}", db_url);

        let endpoint = Channel::from_shared(db_url.clone())
            .with_context(|| format!("Failed to create endpoint from URL: {}", db_url))?;

        let channel = endpoint
            .connect()
            .await
            .with_context(|| format!("Failed to connect to database service at {}", db_url))?;

        let new_client = SealedMemoryDatabaseServiceClient::new(channel);
        *guard = Some(new_client.clone());
        debug!("Successfully created and cached new DB client");
        Ok(new_client)
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

    pub async fn serialize_response(
        &self,
        response: &SealedMemoryResponse,
        message_type: Option<MessageType>,
    ) -> Vec<u8> {
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
        if let Some(message_type) = message_type {
            if message_type == MessageType::Json {
                return serde_json::to_vec(response).unwrap();
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

    pub async fn boot_strap_handler(
        &self,
        request: UserRegistrationRequest,
    ) -> anyhow::Result<UserRegistrationResponse> {
        if request.key_encryption_key.is_empty() {
            bail!("key_encryption_key not set in UserRegistrationRequest");
        }
        if request.pm_uid.is_empty() {
            bail!("pm_uid not set in UserRegistrationRequest");
        }
        let boot_strap_info = request
            .boot_strap_info
            .context("boot_strap_info (KeyDerivationInfo) not set in UserRegistrationRequest")?;

        let key = request.key_encryption_key;
        let uid = request.pm_uid;

        if !Self::is_valid_key(&key) {
            bail!("Not a valid key!");
        }

        let mut db_client = self
            .get_db_client()
            .await
            .context("Failed to get DB client for bootstrap operation")?;

        if let Ok(data_blob) = db_client.get_unencrypted_blob(&uid).await {
            // User already exists
            let plain_text_info = PlainTextUserInfo::decode(&*data_blob.blob)?;
            let key_derivation_info =
                plain_text_info.key_derivation_info.clone().context("Empty key derivation info")?;

            debug!("User have been registered!, {}", uid);
            return Ok(UserRegistrationResponse {
                status: user_registration_response::Status::UserAlreadyExists.into(),
                key_derivation_info: Some(key_derivation_info),
            });
        }

        // User does not exist.
        debug!("Registering new user: {}", uid);

        // Generate a 256-bit key for the user.
        let mut dek = [0u8; 32];
        rand::rng().fill(&mut dek);
        let dek: Vec<u8> = dek.into();
        let nonce = generate_nonce();
        let wrapped_key = EncryptedDataBlob { data: encrypt(&key, &nonce, &dek)?, nonce };

        let new_plain_text_info = PlainTextUserInfo {
            key_derivation_info: Some(boot_strap_info.clone()),
            wrapped_dek: Some(WrappedDataEncryptionKey { wrapped_key: Some(wrapped_key) }),
        };
        let initial_encrypted_info = EncryptedUserInfo { icing_db: None };

        let encrypted_db_blob = encrypt_database(&initial_encrypted_info, &dek)
            .context("Failed to encrypt initial user info")?;

        db_client
            .add_mixed_blobs(
                vec![encrypted_db_blob],
                Some(vec![uid.clone()]),
                vec![DataBlob { id: uid.clone(), blob: new_plain_text_info.encode_to_vec() }],
            )
            .await
            .context("Failed to write blobs")?;

        debug!("Successfully registered new user {}", uid);
        Ok(UserRegistrationResponse {
            status: user_registration_response::Status::Success.into(),
            key_derivation_info: Some(boot_strap_info),
        })
    }

    pub async fn key_sync_handler(
        &self,
        request: KeySyncRequest,
        is_json: bool,
    ) -> anyhow::Result<KeySyncResponse> {
        if request.key_encryption_key.is_empty() || request.pm_uid.is_empty() {
            bail!("uid or key not set in request");
        }
        let key = request.key_encryption_key;
        let uid = request.pm_uid;
        if !Self::is_valid_key(&key) {
            bail!("Not a valid key!");
        }

        if self.session_context().await.is_some() {
            bail!("already setup the session for {uid}");
        }

        let mut db_client =
            self.get_db_client().await.context("Failed to get DB client for key sync")?;
        let database;
        let key_derivation_info;
        let dek: Vec<u8>;

        if let Ok(data_blob) = db_client.get_unencrypted_blob(&uid).await {
            let plain_text_info = PlainTextUserInfo::decode(&*data_blob.blob)?;
            key_derivation_info =
                plain_text_info.key_derivation_info.clone().context("Empty key derivation info")?;
            let wrapped_dek = plain_text_info
                .wrapped_dek
                .clone()
                .context("Empty wrapped dek")?
                .wrapped_key
                .clone()
                .context("Empty wrapped dek")?;
            dek = decrypt(&key, &wrapped_dek.nonce, &wrapped_dek.data)?;
        } else {
            return Ok(KeySyncResponse { status: key_sync_response::Status::InvalidPmUid.into() });
        }
        if let Ok(data_blob) = db_client.get_blob(&uid).await {
            let encrypted_info = decrypt_database(data_blob, &dek)?;
            database = if encrypted_info.icing_db.is_some() {
                IcingMetaDatabase::import(
                    &encrypted_info.icing_db.clone().unwrap().encode_to_vec(),
                    None,
                )?
            } else {
                let temp_path = tempfile::tempdir()?.path().to_str().unwrap().to_string();
                IcingMetaDatabase::new(&temp_path)?
            };
            debug!("Loaded database successfully!!");
        } else {
            debug!("no blob for {}", uid);
            return Ok(KeySyncResponse { status: key_sync_response::Status::InvalidPmUid.into() });
        };

        let message_type = if is_json { MessageType::Json } else { MessageType::BinaryProto };
        let mut mutex_guard = self.session_context().await;
        *mutex_guard = Some(UserSessionContext {
            dek: dek.clone(),
            uid,
            message_type,
            database_service_client: db_client.clone(),
            database: DatabaseWithCache::new(database, dek, db_client, key_derivation_info),
        });

        Ok(KeySyncResponse { status: key_sync_response::Status::Success.into() })
    }

    pub async fn search_memory_handler(
        &self,
        request: SearchMemoryRequest,
    ) -> anyhow::Result<SearchMemoryResponse> {
        let mut mutex_guard = self.session_context().await;
        let context: &mut Option<UserSessionContext> = &mut mutex_guard;
        if let Some(context) = context {
            let search_query_container =
                request.query.context("SearchMemoryRequest must contain a 'query' field")?;

            let embedding_query_details = match search_query_container.clause {
                Some(
                    sealed_memory_rust_proto::oak::private_memory::search_memory_query::Clause::EmbeddingQuery(
                        eq,
                    ),
                ) => eq,
                None => bail!("SearchMemoryQuery must contain a 'clause'"),
            };

            let search_embeddings = &embedding_query_details.embedding;
            let score_range = embedding_query_details.score_range;

            let database = &mut context.database;
            const MAX_RESULTS: u32 = 100;
            let limit = MAX_RESULTS;
            let results = database.search_memory(search_embeddings, limit, score_range).await;
            Ok(SearchMemoryResponse { results })
        } else {
            bail!("You need to call key sync first")
        }
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
impl_packing!(Request => SearchMemoryRequest);
impl_packing!(Request => UserRegistrationRequest);
impl_packing!(Response => AddMemoryResponse);
impl_packing!(Response => GetMemoriesResponse);
impl_packing!(Response => ResetMemoryResponse);
impl_packing!(Response => InvalidRequestResponse);
impl_packing!(Response => KeySyncResponse);
impl_packing!(Response => GetMemoryByIdResponse);
impl_packing!(Response => SearchMemoryResponse);
impl_packing!(Response => UserRegistrationResponse);

#[async_trait::async_trait]
impl ApplicationHandler for SealedMemoryHandler {
    /// This implementation is quite simple, since there's just a single request
    /// that is a string. In a real implementation, we'd probably
    /// deserialize into a proto, and dispatch to various handlers from
    /// there.
    async fn handle(&self, request_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        let request = self.deserialize_request(request_bytes).await;
        let mut message_type = None;
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
                sealed_memory_request::Request::UserRegistrationRequest(request) => {
                    if self.is_message_type_json(request_bytes) {
                        message_type = Some(MessageType::Json);
                    }
                    self.boot_strap_handler(request).await?.into_response()
                }
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
                sealed_memory_request::Request::SearchMemoryRequest(request) => {
                    self.search_memory_handler(request).await?.into_response()
                }
            };
            response.request_id = request_id;
            response
        };

        Ok(self.serialize_response(&response, message_type).await)
    }
}
