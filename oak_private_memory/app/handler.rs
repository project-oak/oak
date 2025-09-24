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
//
use std::sync::Arc;

use anyhow::{bail, Context};
use encryption::{decrypt, encrypt, generate_nonce};
use external_db_client::{BlobId, DataBlobHandler};
use log::{debug, info};
use metrics::{get_global_metrics, RequestMetricName};
use oak_private_memory_database::{
    encryption::decrypt_database, DatabaseWithCache, IcingMetaDatabase, IcingTempDir, MemoryId,
    PageToken,
};
use prost::Message;
use rand::Rng;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use sealed_memory_rust_proto::prelude::v1::*;
use tokio::{
    sync::{mpsc, Mutex, MutexGuard},
    time::Instant,
};
use tonic::transport::Channel;

use crate::{
    context::UserSessionContext, db_client::SharedDbClient, packing::ResponsePacking, MessageType,
};
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

        database.reset_memory().await?;
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

        db_client
            .add_unencrypted_blob(
                DataBlob { id: uid.clone(), blob: new_plain_text_info.encode_to_vec() },
                None,
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
            let db = IcingMetaDatabase::import(
                IcingTempDir::new("sm-server-icing-"),
                icing_db.encode_to_vec().as_slice(),
            )?;
            let elapsed = now.elapsed();
            get_global_metrics().record_db_init_latency(elapsed.as_millis() as u64);
            return Ok(db);
        }
    } else {
        debug!("no blob for {}", uid);
    }

    // This case can happen if the user is just registered, but the initial database
    // has not been created, or if the blob exists but is empty.
    let db = IcingMetaDatabase::new(IcingTempDir::new("sm-server-icing-"))?;
    Ok(db)
}
