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

use std::{net::SocketAddr, sync::Arc};

pub mod app_service;

use anyhow::{bail, Context};
use encryption::{decrypt, encrypt, generate_nonce};
use external_db_client::{BlobId, DataBlobHandler};
use log::{debug, info};
use metrics::{get_global_metrics, RequestMetricName};
use oak_private_memory_database::{
    encryption::{decrypt_database, encrypt_database},
    DatabaseWithCache, IcingMetaDatabase, MemoryId, PageToken,
};
use prost::Message;
use rand::Rng;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use sealed_memory_rust_proto::prelude::v1::*;
use tempfile::tempdir;
use tokio::{
    sync::{mpsc, Mutex, MutexGuard, RwLock},
    time::Instant,
};
use tonic::transport::{Channel, Endpoint};

const MAX_CONNECT_RETRIES: usize = 5;
const INITIAL_BACKOFF_MS: u64 = 100;
const MAX_DECODE_SIZE: usize = 10 * 1024 * 1024; // 10 MB

pub struct SharedDbClient {
    database_service_host: SocketAddr,
    client: RwLock<Option<SealedMemoryDatabaseServiceClient<Channel>>>,
}

impl SharedDbClient {
    pub fn new(database_service_host: SocketAddr) -> Self {
        Self { database_service_host, client: RwLock::new(None) }
    }

    pub async fn get_or_connect(
        &self,
    ) -> anyhow::Result<SealedMemoryDatabaseServiceClient<Channel>> {
        // First, try to get a read lock and check if the client is already initialized.
        {
            let read_guard = self.client.read().await;
            if let Some(client) = read_guard.as_ref() {
                info!("Reusing cached DB client");
                return Ok(client.clone());
            }
        }

        // If the client is not initialized, get a write lock to initialize it.
        let mut write_guard = self.client.write().await;
        // Check again in case another thread initialized it while we were waiting for
        // the write lock.
        if let Some(client) = write_guard.as_ref() {
            info!("Reusing cached DB client initialized by another thread");
            return Ok(client.clone());
        }

        let mut backoff = INITIAL_BACKOFF_MS;
        let db_addr = self.database_service_host;
        let db_url = format!("http://{db_addr}");
        info!("Database service URL: {}", db_url);
        let endpoint = Endpoint::from_shared(db_url.clone())?;
        for attempt in 0..MAX_CONNECT_RETRIES {
            info!("Creating new DB client, attempt {}", attempt + 1);

            match endpoint.connect().await {
                Ok(channel) => {
                    let new_client = SealedMemoryDatabaseServiceClient::new(channel)
                        .max_decoding_message_size(MAX_DECODE_SIZE);
                    *write_guard = Some(new_client.clone());
                    info!("Successfully created and cached new DB client");
                    return Ok(new_client);
                }
                Err(err) => {
                    info!("Failed to connect to database service: {}", err);
                }
            }

            tokio::time::sleep(tokio::time::Duration::from_millis(backoff)).await;
            backoff *= 2;
            get_global_metrics().inc_db_connect_retries();
        }
        bail!("Failed to connect to database service after {} attempts", MAX_CONNECT_RETRIES);
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

async fn persist_database(user_context: &mut UserSessionContext) -> anyhow::Result<()> {
    if !user_context.database.changed() {
        info!("Database is not changed, skip saving");
        return Ok(());
    }

    let exported_db = user_context.database.export()?;
    let encrypted_info = exported_db.encrypted_info.context("Encrypted info is empty")?;
    let database = encrypt_database(&encrypted_info, &user_context.dek)?;

    let db_size = database.data.len() as u64;
    info!("Saving db size: {}", db_size);
    get_global_metrics().record_db_size(db_size);

    let now = Instant::now();
    user_context.database_service_client.add_blob(database, Some(user_context.uid.clone())).await?;
    let elapsed = now.elapsed();
    get_global_metrics().record_db_persist_latency(elapsed.as_millis() as u64);

    Ok(())
}

pub async fn run_persistence_service(mut rx: mpsc::UnboundedReceiver<UserSessionContext>) {
    info!("Persistence service started");
    while let Some(mut user_context) = rx.recv().await {
        info!("Persistence service received a session to save");
        get_global_metrics().record_db_persist_queue_size(rx.len() as u64);
        if let Err(e) = persist_database(&mut user_context).await {
            get_global_metrics().inc_db_persist_failures();
            info!("Failed to persist database: {:?}", e);
        }
    }
    info!("Persistence service finished");
}

async fn get_or_create_db(
    db_client: &mut SealedMemoryDatabaseServiceClient<Channel>,
    uid: &BlobId,
    dek: &[u8],
) -> anyhow::Result<IcingMetaDatabase> {
    if let Some(data_blob) = db_client.get_blob(uid, true).await? {
        info!("Loaded database from blob: Length: {}", data_blob.data.len());
        let encrypted_info = decrypt_database(data_blob, dek)?;
        if let Some(icing_db) = encrypted_info.icing_db {
            let now = Instant::now();
            info!("Loaded database successfully!!");
            let temp_dir = tempdir()?;
            let db = IcingMetaDatabase::import(temp_dir, icing_db.encode_to_vec().as_slice())?;
            let elapsed = now.elapsed();
            get_global_metrics().record_db_init_latency(elapsed.as_millis() as u64);
            return Ok(db);
        }
    } else {
        debug!("no blob for {}", uid);
    }

    // This case can happen if the user is just registered, but the initial database
    // has not been created, or if the blob exists but is empty.
    let temp_path = tempfile::tempdir()?.path().to_str().context("invalid temp path")?.to_string();
    let db = IcingMetaDatabase::new(&temp_path)?;
    Ok(db)
}

// The implementation for one active Oak Private Memory session.
// A new instances of this struct is created per-request.
pub struct SealedMemorySessionHandler {
    session_context: Mutex<Option<UserSessionContext>>,
    db_client: Arc<SharedDbClient>,
    metrics: Arc<metrics::Metrics>,
    persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
}

impl Drop for SealedMemorySessionHandler {
    fn drop(&mut self) {
        info!("Dropping handler and sending session context to persistence service");
        if let Some(context) = self.session_context.get_mut().take() {
            if let Err(e) = self.persistence_tx.send(context) {
                info!("Failed to send session context to persistence service: {}", e);
            }
        }
    }
}

impl SealedMemorySessionHandler {
    pub fn new(
        metrics: Arc<metrics::Metrics>,
        persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
        db_client: Arc<SharedDbClient>,
    ) -> Self {
        Self { session_context: Default::default(), db_client, metrics, persistence_tx }
    }

    pub async fn session_context(&self) -> MutexGuard<'_, Option<UserSessionContext>> {
        self.session_context.lock().await
    }

    pub fn is_message_type_json(&self, request_bytes: &[u8]) -> bool {
        serde_json::from_slice::<SealedMemoryRequest>(request_bytes).is_ok()
    }

    async fn session_message_type(&self) -> Option<MessageType> {
        let guarded_session = self.session_context().await;
        guarded_session.as_ref().map(|session| session.message_type)
    }

    pub async fn deserialize_request(
        &self,
        request_bytes: &[u8],
    ) -> anyhow::Result<SealedMemoryRequest> {
        Ok(match self.session_message_type().await {
            Some(MessageType::BinaryProto) => SealedMemoryRequest::decode(request_bytes)?,
            Some(MessageType::Json) => {
                serde_json::from_slice::<SealedMemoryRequest>(request_bytes)?
            }
            None => {
                // Default to trying all the options.
                if let Ok(request) = SealedMemoryRequest::decode(request_bytes) {
                    info!("Request is in binary proto format");
                    request
                } else if let Ok(request) =
                    serde_json::from_slice::<SealedMemoryRequest>(request_bytes)
                {
                    info!("Request is in json format {:?}", request);
                    request
                } else {
                    anyhow::bail!("The provided request could not be decoded with any strategy")
                }
            }
        })
    }

    pub async fn serialize_response(
        &self,
        response: &SealedMemoryResponse,
        message_type: Option<MessageType>,
    ) -> anyhow::Result<Vec<u8>> {
        let message_type = self
            .session_message_type()
            .await
            // If no session, use the caller-provided type.
            // If no caller-provided type, default to binaryproto.
            .unwrap_or(message_type.unwrap_or(MessageType::BinaryProto));

        Ok(match message_type {
            MessageType::BinaryProto => response.encode_to_vec(),
            MessageType::Json => serde_json::to_vec(response)?,
        })
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
        let database = &mut mutex_guard.as_mut().context("call key sync first")?.database;
        let memory = request.memory.context("memory not set in AddMemoryRequest")?;

        let memory_id = database.add_memory(memory).await?;
        Ok(AddMemoryResponse { id: memory_id.to_string() })
    }

    pub async fn get_memories_handler(
        &self,
        request: GetMemoriesRequest,
    ) -> anyhow::Result<GetMemoriesResponse> {
        let mut mutex_guard = self.session_context().await;
        let database = &mut mutex_guard.as_mut().context("call key sync first")?.database;

        let page_token = PageToken::try_from(request.page_token)
            .map_err(|e| anyhow::anyhow!("Invalid page token: {}", e))?;
        let (memories, next_page_token) = database
            .get_memories_by_tag(&request.tag, &request.result_mask, request.page_size, page_token)
            .await?;
        Ok(GetMemoriesResponse { memories, next_page_token: next_page_token.into() })
    }

    pub async fn get_memory_by_id_handler(
        &self,
        request: GetMemoryByIdRequest,
    ) -> anyhow::Result<GetMemoryByIdResponse> {
        let mut mutex_guard = self.session_context().await;
        let database = &mut mutex_guard.as_mut().context("call key sync first")?.database;

        let memory = database.get_memory_by_id(request.id, &request.result_mask).await?;
        let success = memory.is_some();
        Ok(GetMemoryByIdResponse { memory, success })
    }

    pub async fn reset_memory_handler(
        &self,
        _request: ResetMemoryRequest,
    ) -> anyhow::Result<ResetMemoryResponse> {
        let mut mutex_guard = self.session_context().await;
        let database = &mut mutex_guard.as_mut().context("call key sync first")?.database;

        database.reset_memory().await;
        Ok(ResetMemoryResponse { success: true, ..Default::default() })
    }

    async fn setup_user_session_context(
        &self,
        uid: String,
        dek: Vec<u8>,
        key_derivation_info: KeyDerivationInfo,
        mut db_client: SealedMemoryDatabaseServiceClient<Channel>,
        is_json: bool,
    ) -> anyhow::Result<()> {
        let database = get_or_create_db(&mut db_client, &uid, &dek).await?;

        let message_type = if is_json { MessageType::Json } else { MessageType::BinaryProto };
        let mut mutex_guard = self.session_context().await;
        let database =
            DatabaseWithCache::new(database, dek.clone(), db_client.clone(), key_derivation_info);

        *mutex_guard = Some(UserSessionContext {
            dek,
            uid,
            message_type,
            database_service_client: db_client,
            database,
        });
        Ok(())
    }

    pub async fn boot_strap_handler(
        &self,
        request: UserRegistrationRequest,
        is_json: bool,
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
            .db_client
            .get_or_connect()
            .await
            .context("Failed to get DB client for bootstrap operation")?;

        if let Some(data_blob) = db_client.get_unencrypted_blob(&uid, true).await? {
            // User already exists
            let plain_text_info = PlainTextUserInfo::decode(&*data_blob.blob)
                .context("Failed to decode PlainTextUserInfo")?;
            let key_derivation_info =
                plain_text_info.key_derivation_info.clone().context("Empty key derivation info")?;

            info!("User have been registered!, {}", uid);
            return Ok(UserRegistrationResponse {
                status: user_registration_response::Status::UserAlreadyExists.into(),
                key_derivation_info: Some(key_derivation_info),
            });
        }

        // User does not exist.
        info!("Registering new user: {}", uid);

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

        info!("Successfully registered new user {}", uid);
        self.setup_user_session_context(
            uid.clone(),
            dek,
            boot_strap_info.clone(),
            db_client,
            is_json,
        )
        .await?;
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
        if self.session_context().await.is_some() {
            info!("session already setup");
            return Ok(KeySyncResponse { status: key_sync_response::Status::Success.into() });
        }

        if request.key_encryption_key.is_empty() || request.pm_uid.is_empty() {
            bail!("uid or key not set in request");
        }
        let key = request.key_encryption_key;
        let uid = request.pm_uid;
        if !Self::is_valid_key(&key) {
            bail!("Not a valid key!");
        }

        let db_client = self
            .db_client
            .get_or_connect()
            .await
            .context("Failed to get DB client for key sync")?;
        let key_derivation_info;
        let dek: Vec<u8>;

        if let Some(data_blob) = db_client.clone().get_unencrypted_blob(&uid, true).await? {
            let plain_text_info = PlainTextUserInfo::decode(&*data_blob.blob)
                .context("Failed to decode PlainTextUserInfo")?;
            key_derivation_info =
                plain_text_info.key_derivation_info.clone().context("Empty key derivation info")?;
            let wrapped_dek = plain_text_info
                .wrapped_dek
                .clone()
                .context("Empty wrapped dek")?
                .wrapped_key
                .clone()
                .context("Empty wrapped dek")?;
            dek = decrypt(&key, &wrapped_dek.nonce, &wrapped_dek.data)
                .context("Failed to decrypt DEK")?;
        } else {
            return Ok(KeySyncResponse { status: key_sync_response::Status::InvalidPmUid.into() });
        }

        self.setup_user_session_context(uid, dek, key_derivation_info, db_client, is_json)
            .await
            .context("Failed to setup user session context")?;

        Ok(KeySyncResponse { status: key_sync_response::Status::Success.into() })
    }

    pub async fn search_memory_handler(
        &self,
        request: SearchMemoryRequest,
    ) -> anyhow::Result<SearchMemoryResponse> {
        let mut mutex_guard = self.session_context().await;
        let database = &mut mutex_guard.as_mut().context("call key sync first")?.database;

        // The extraction of embedding details is now done in
        // IcingMetaDatabase::embedding_search
        let (results, next_page_token) = database.search_memory(request).await?;
        Ok(SearchMemoryResponse { results, next_page_token: next_page_token.into() })
    }

    pub async fn delete_memory_handler(
        &self,
        request: DeleteMemoryRequest,
    ) -> anyhow::Result<DeleteMemoryResponse> {
        let mut mutex_guard = self.session_context().await;
        let database = &mut mutex_guard.as_mut().context("call key sync first")?.database;

        let memory_ids: Vec<MemoryId> = request.ids.into_iter().collect();
        Ok(DeleteMemoryResponse {
            success: database.delete_memories(memory_ids).await.is_ok(),
            ..Default::default()
        })
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
    (Request => DeleteMemoryRequest) => {
        impl RequestUnpacking for DeleteMemoryRequest {
            fn from_request(x: SealedMemoryRequest) -> Option<Self> {
                match x.request {
                    Some(sealed_memory_request::Request::DeleteMemoryRequest(request)) => {
                        Some(request)
                    }
                    _ => None,
                }
            }

            fn into_request(self) -> SealedMemoryRequest {
                SealedMemoryRequest {
                    request: Some(sealed_memory_request::Request::DeleteMemoryRequest(self)),
                    request_id: 0,
                }
            }
        }
    };

    (Response => DeleteMemoryResponse) => {
        impl ResponsePacking for DeleteMemoryResponse {
            fn from_response(x: SealedMemoryResponse) -> Option<Self> {
                match x.response {
                    Some(sealed_memory_response::Response::DeleteMemoryResponse(response)) => {
                        Some(response)
                    }
                    _ => None,
                }
            }

            fn into_response(self) -> SealedMemoryResponse {
                SealedMemoryResponse {
                    response: Some(sealed_memory_response::Response::DeleteMemoryResponse(self)),
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
impl_packing!(Request => DeleteMemoryRequest);

impl_packing!(Response => AddMemoryResponse);
impl_packing!(Response => GetMemoriesResponse);
impl_packing!(Response => ResetMemoryResponse);
impl_packing!(Response => InvalidRequestResponse);
impl_packing!(Response => KeySyncResponse);
impl_packing!(Response => GetMemoryByIdResponse);
impl_packing!(Response => SearchMemoryResponse);
impl_packing!(Response => DeleteMemoryResponse);
impl_packing!(Response => UserRegistrationResponse);

impl SealedMemorySessionHandler {
    /// This implementation is quite simple, since there's just a single request
    /// that is a string. In a real implementation, we'd probably
    /// deserialize into a proto, and dispatch to various handlers from
    /// there.
    pub async fn handle(&self, request_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        let request = self
            .deserialize_request(request_bytes)
            .await
            .context("failed to deserialize request")?;
        let mut message_type = None;

        let request_id = request.request_id;
        let request_variant = request.request.context("The request is empty. The json format might be incorrect: the data type should strictly match.")?;

        let metric_name = RequestMetricName::new_sealed_memory_request(&request_variant);
        self.metrics.inc_requests(metric_name.clone());

        let start_time = Instant::now();
        let mut response = match request_variant {
            sealed_memory_request::Request::UserRegistrationRequest(request) => {
                let is_json = self.is_message_type_json(request_bytes);
                if is_json {
                    message_type = Some(MessageType::Json);
                };
                self.boot_strap_handler(request, is_json).await?.into_response()
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
            sealed_memory_request::Request::DeleteMemoryRequest(request) => {
                self.delete_memory_handler(request).await?.into_response()
            }
        };
        let elapsed_time = start_time.elapsed().as_millis() as u64;
        self.metrics.record_latency(elapsed_time, metric_name);
        response.request_id = request_id;

        self.serialize_response(&response, message_type).await
    }
}
