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

use encryption::{decrypt, encrypt, generate_nonce};
use external_db_client::{BlobId, DataBlobHandler};
use log::{debug, info, warn};
use metrics::{RequestMetricName, get_global_metrics};
use oak_private_memory_database::{
    IcingTempDir, MemoryId,
    clock::Clock,
    database::Database,
    encryption::decrypt_database,
    icing::{IcingDatabaseConfig, IcingMetaDatabase, PageToken},
};
use prost::Message;
use rand::Rng;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use sealed_memory_rust_proto::prelude::v1::*;
use tokio::{
    sync::{RwLock, RwLockReadGuard, RwLockWriteGuard, mpsc},
    time::Instant,
};
use tonic::transport::Channel;

use crate::{
    IntoTonicResult, context::UserSessionContext, db_client::SharedDbClient,
    packing::ResponsePacking, persistence_worker,
};
/// Controls how errors are propagated to the client.
///
/// Note: The header-based configuration and `PropagateAsGrpcStatus` behavior
/// are only for migration purposes. Once all clients move to the new
/// in-response error handling (`PropagateInResponseProto`), we will make it the
/// default and remove the header support.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorPropagationBehavior {
    PropagateAsGrpcStatus = 0,
    PropagateInResponseProto = 1,
}

// The implementation for one active Oak Private Memory session.
// A new instances of this struct is created per-request.
pub struct SealedMemorySessionHandler {
    session_context: RwLock<Option<UserSessionContext>>,
    db_client: Arc<SharedDbClient>,
    metrics: Arc<metrics::Metrics>,
    persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
    clock: Arc<dyn Clock>,
    error_propagation_behavior: ErrorPropagationBehavior,
    max_database_size_bytes: usize,
    blanket_ttl_seconds: i64,
    max_memory_ttl_seconds: i64,
    enable_int8_embedding: bool,
    allowed_memory_sources: Vec<String>,
}

impl Drop for SealedMemorySessionHandler {
    fn drop(&mut self) {
        if let Some(context) = self.session_context.get_mut().take() {
            if context.disable_persistence_on_close {
                info!("persistence disabled for this session, skipping");
                return;
            }
            info!("sending session context to persistence service");
            if let Err(e) = self.persistence_tx.send(context) {
                self.metrics.inc_persistence_enqueue_failures();
                warn!("failed to send session context to persistence service: {}", e);
            }
        }
    }
}

impl SealedMemorySessionHandler {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        metrics: Arc<metrics::Metrics>,
        persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
        db_client: Arc<SharedDbClient>,
        clock: Arc<dyn Clock>,
        error_propagation_behavior: ErrorPropagationBehavior,
        max_database_size_bytes: usize,
        blanket_ttl_seconds: i64,
        max_memory_ttl_seconds: i64,
        enable_int8_embedding: bool,
        allowed_memory_sources: Vec<String>,
    ) -> Self {
        Self {
            session_context: Default::default(),
            db_client,
            metrics,
            persistence_tx,
            clock,
            error_propagation_behavior,
            max_database_size_bytes,
            blanket_ttl_seconds,
            max_memory_ttl_seconds,
            enable_int8_embedding,
            allowed_memory_sources,
        }
    }

    pub async fn session_context(&self) -> RwLockWriteGuard<'_, Option<UserSessionContext>> {
        self.session_context.write().await
    }

    async fn session_context_read(&self) -> RwLockReadGuard<'_, Option<UserSessionContext>> {
        self.session_context.read().await
    }

    pub fn deserialize_request(&self, request_bytes: &[u8]) -> anyhow::Result<SealedMemoryRequest> {
        Ok(SealedMemoryRequest::decode(request_bytes)?)
    }

    pub fn serialize_response(&self, response: &SealedMemoryResponse) -> anyhow::Result<Vec<u8>> {
        Ok(response.encode_to_vec())
    }

    fn validate_expiration_timestamp(
        &self,
        expiration_timestamp: Option<&prost_types::Timestamp>,
    ) -> tonic::Result<()> {
        let expiration =
            expiration_timestamp.into_invalid_argument("expiration_timestamp must be set")?;

        let now_ts = oak_private_memory_database::clock::system_time_to_timestamp(self.clock.now());

        // Validate that the expiration timestamp is strictly in the future.
        if expiration.seconds < now_ts.seconds
            || (expiration.seconds == now_ts.seconds && expiration.nanos < now_ts.nanos)
        {
            return Err(tonic::Status::invalid_argument(
                "expiration_timestamp must be in the future",
            ));
        }

        // Add a consolidated buffer to accommodate potential clock drift.
        let clock_drift_buffer_seconds =
            oak_private_memory_database::clock::CLOCK_DRIFT_BUFFER_SECONDS;
        let max_expiration_seconds =
            now_ts.seconds + self.max_memory_ttl_seconds + clock_drift_buffer_seconds;

        if expiration.seconds > max_expiration_seconds
            || (expiration.seconds == max_expiration_seconds && expiration.nanos > now_ts.nanos)
        {
            let error_msg = if self.max_memory_ttl_seconds == crate::MAX_MEMORY_TTL_SECONDS {
                "expiration_timestamp cannot be more than 2 years in the future".to_string()
            } else {
                format!(
                    "expiration_timestamp cannot be more than {} seconds in the future",
                    self.max_memory_ttl_seconds
                )
            };
            return Err(tonic::Status::invalid_argument(error_msg));
        }

        Ok(())
    }

    /// Validates the memory's source against the configured allowlist.
    ///
    /// When `allowed_memory_sources` is non-empty, every memory must have a
    /// `source` with a `source_id` that appears in the allowlist. Returns
    /// `InvalidArgument` if the source is missing or not in the list.
    fn validate_memory_source(&self, memory: &Memory) -> tonic::Result<()> {
        if self.allowed_memory_sources.is_empty() {
            return Ok(());
        }

        let source = memory.source.as_ref().ok_or_else(|| {
            tonic::Status::invalid_argument(
                "memory source is required when source allowlist is configured",
            )
        })?;

        if source.source_id.is_empty() {
            return Err(tonic::Status::invalid_argument("memory source_id must not be empty"));
        }

        if !self.allowed_memory_sources.contains(&source.source_id) {
            return Err(tonic::Status::invalid_argument(format!(
                "memory source_id '{}' is not in the allowed sources list",
                source.source_id
            )));
        }

        Ok(())
    }

    fn is_valid_key(key: &[u8]) -> bool {
        // Only support 256-bit key for now.
        key.len() == 32
    }

    // Memory related handlers

    pub async fn add_memory_handler(
        &self,
        request: AddMemoryRequest,
    ) -> tonic::Result<AddMemoryResponse> {
        let mut mutex_guard = self.session_context().await;
        let database =
            &mut mutex_guard.as_mut().into_failed_precondition("call key sync first")?.database;
        let memory = request.memory.into_invalid_argument("memory not set in AddMemoryRequest")?;

        self.validate_memory_source(&memory)?;
        self.validate_expiration_timestamp(memory.expiration_timestamp.as_ref())?;

        if !memory.name.is_empty() {
            // Verify that there is no conflicting memory with this name.
            let existing_memory = database
                .get_memory_by_name(&memory.name, &None)
                .await
                .into_internal_error("failed to check for existing named memory")?;
            if let Some(existing_memory) = existing_memory
                && existing_memory.id != memory.id
            {
                return Err(tonic::Status::invalid_argument(format!(
                    "Existing memory with name {}, existing {} -> new {}",
                    memory.name, existing_memory.id, memory.id
                )));
            }
        }

        let memory_id =
            database.add_memory(memory).await.into_internal_error("failed to add memory")?;
        Ok(AddMemoryResponse { id: memory_id.to_string() })
    }

    pub async fn get_memories_handler(
        &self,
        request: GetMemoriesRequest,
    ) -> tonic::Result<GetMemoriesResponse> {
        let guard = self.session_context_read().await;
        let database = &guard.as_ref().into_failed_precondition("call key sync first")?.database;

        let page_token =
            PageToken::try_from(request.page_token).into_invalid_argument("invalid page token")?;
        let (memories, next_page_token) = database
            .get_memories_by_tag(&request.tag, &request.result_mask, request.page_size, page_token)
            .await
            .into_internal_error("failed to get memories by tag")?;
        Ok(GetMemoriesResponse { memories, next_page_token: next_page_token.into() })
    }

    pub async fn get_memory_by_id_handler(
        &self,
        request: GetMemoryByIdRequest,
    ) -> tonic::Result<GetMemoryByIdResponse> {
        let guard = self.session_context_read().await;
        let database = &guard.as_ref().into_failed_precondition("call key sync first")?.database;

        let memory = database
            .get_memory_by_id(request.id, &request.result_mask)
            .await
            .into_internal_error("failed to get memory by id")?;
        let success = memory.is_some();
        Ok(GetMemoryByIdResponse { memory, success })
    }

    pub async fn get_memories_by_id_handler(
        &self,
        request: GetMemoriesByIdRequest,
    ) -> tonic::Result<GetMemoriesByIdResponse> {
        let guard = self.session_context_read().await;
        let database = &guard.as_ref().into_failed_precondition("call key sync first")?.database;
        let (memories, not_found_ids) = database
            .get_memories_by_id(request.ids, &request.result_mask)
            .await
            .into_internal_error("failed to get memories by id")?;
        Ok(GetMemoriesByIdResponse { memories, not_found_ids })
    }

    pub async fn get_memory_by_name_handler(
        &self,
        request: GetMemoryByNameRequest,
    ) -> tonic::Result<GetMemoryByNameResponse> {
        let guard = self.session_context_read().await;
        let database = &guard.as_ref().into_failed_precondition("call key sync first")?.database;
        let memory = database
            .get_memory_by_name(&request.name, &request.result_mask)
            .await
            .into_internal_error("failed to get memory by name")?;
        let success = memory.is_some();
        Ok(GetMemoryByNameResponse { memory, success })
    }

    pub async fn reset_memory_handler(
        &self,
        _request: ResetMemoryRequest,
    ) -> tonic::Result<ResetMemoryResponse> {
        let mut mutex_guard = self.session_context().await;
        let database =
            &mut mutex_guard.as_mut().into_failed_precondition("call key sync first")?.database;

        database.reset_memory().await.into_internal_error("failed to reset memory")?;
        Ok(ResetMemoryResponse { success: true, ..Default::default() })
    }

    async fn setup_user_session_context(
        &self,
        uid: String,
        dek: Vec<u8>,
        key_derivation_info: KeyDerivationInfo,
        mut db_client: SealedMemoryDatabaseServiceClient<Channel>,
        disable_persistence_on_close: bool,
    ) -> tonic::Result<()> {
        let (database, database_version, initial_size) = get_or_create_db(
            &mut db_client,
            &uid,
            &dek,
            self.clock.clone(),
            self.blanket_ttl_seconds,
            self.enable_int8_embedding,
        )
        .await?;

        let mut mutex_guard = self.session_context().await;
        let database = Database::new(
            database,
            dek.clone(),
            db_client.clone(),
            key_derivation_info,
            initial_size,
            self.blanket_ttl_seconds,
        )
        .with_max_size(self.max_database_size_bytes)
        .with_clock(self.clock.clone());

        *mutex_guard = Some(UserSessionContext {
            dek,
            uid,
            database_service_client: db_client,
            database_version,
            database,
            disable_persistence_on_close,
        });
        Ok(())
    }

    pub async fn user_registration_handler(
        &self,
        request: UserRegistrationRequest,
    ) -> tonic::Result<UserRegistrationResponse> {
        if request.key_encryption_key.is_empty() {
            return Err(tonic::Status::invalid_argument(
                "key_encryption_key not set in UserRegistrationRequest",
            ));
        }
        if request.pm_uid.is_empty() {
            return Err(tonic::Status::invalid_argument(
                "pm_uid not set in UserRegistrationRequest",
            ));
        }
        let boot_strap_info = request.boot_strap_info.into_invalid_argument(
            "boot_strap_info (KeyDerivationInfo) not set in UserRegistrationRequest",
        )?;

        let key = request.key_encryption_key;
        let uid = request.pm_uid;

        if !Self::is_valid_key(&key) {
            return Err(tonic::Status::invalid_argument(
                "Invalid key length in key_encryption_key: only 256-bit key is supported",
            ));
        }

        let mut db_client = self
            .db_client
            .get_or_connect()
            .await
            .into_internal_error("Failed to get DB client for bootstrap operation")?;

        if let Some(data_blob) = db_client
            .get_unencrypted_blob(&uid, true)
            .await
            .into_internal_error("Failed to get unencrypted blob")?
        {
            let plain_text_info = PlainTextUserInfo::decode(&*data_blob.blob)
                .inspect_err(|_| self.metrics.inc_user_info_deserialization_failures())
                .into_internal_error("Failed to decode PlainTextUserInfo")?;
            let key_derivation_info = plain_text_info
                .key_derivation_info
                .clone()
                .into_internal_error("Empty key derivation info")?;

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
        let wrapped_key = EncryptedDataBlob {
            data: encrypt(&key, &nonce, &dek, b"")
                .into_internal_error("failed to encrypt data blob")?,
            nonce,
        };

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
            .into_internal_error("Failed to write blobs")?;

        info!("Successfully registered new user {}", uid);
        // All errors from setup_user_session_context are infrastructure failures
        // (DB fetch, decryption, import) outside the caller's control.
        self.setup_user_session_context(
            uid.clone(),
            dek,
            boot_strap_info.clone(),
            db_client,
            false,
        )
        .await
        .into_internal_error("Failed to setup user session context")?;
        Ok(UserRegistrationResponse {
            status: user_registration_response::Status::Success.into(),
            key_derivation_info: Some(boot_strap_info),
        })
    }

    pub async fn key_sync_handler(
        &self,
        request: KeySyncRequest,
    ) -> tonic::Result<KeySyncResponse> {
        if request.key_encryption_key.is_empty() || request.pm_uid.is_empty() {
            return Ok(KeySyncResponse { status: key_sync_response::Status::InvalidPmUid.into() });
        }
        let key = request.key_encryption_key;
        let uid = request.pm_uid;
        if !Self::is_valid_key(&key) {
            return Ok(KeySyncResponse { status: key_sync_response::Status::InvalidKey.into() });
        }

        let disable_persistence_on_close =
            request.session_config.map(|c| c.disable_persistence_on_close).unwrap_or(false);

        let mut db_client = self
            .db_client
            .get_or_connect()
            .await
            .into_internal_error("Failed to get DB client for key sync")?;
        let key_derivation_info;
        let dek: Vec<u8>;

        if let Some(data_blob) = db_client
            .get_unencrypted_blob(&uid, true)
            .await
            .into_internal_error("Failed to get unencrypted blob")?
        {
            let plain_text_info = PlainTextUserInfo::decode(&*data_blob.blob)
                .inspect_err(|_| self.metrics.inc_user_info_deserialization_failures())
                .into_internal_error("Failed to decode PlainTextUserInfo")?;
            key_derivation_info = plain_text_info
                .key_derivation_info
                .clone()
                .into_internal_error("Empty key derivation info")?;
            let wrapped_dek = plain_text_info
                .wrapped_dek
                .clone()
                .into_internal_error("Empty wrapped dek")?
                .wrapped_key
                .clone()
                .into_internal_error("Empty wrapped dek")?;
            dek = if let Ok(dek) = decrypt(&key, &wrapped_dek.nonce, &wrapped_dek.data, b"") {
                dek
            } else {
                self.metrics.inc_decrypt_dek_failures();
                return Ok(KeySyncResponse {
                    status: key_sync_response::Status::InvalidKey.into(),
                });
            }
        } else {
            return Ok(KeySyncResponse { status: key_sync_response::Status::InvalidPmUid.into() });
        }

        self.setup_user_session_context(
            uid,
            dek,
            key_derivation_info,
            db_client,
            disable_persistence_on_close,
        )
        .await
        .into_internal_error("Failed to setup user session context")?;

        let cleanup_start_time = Instant::now();
        self.clean_expired_memories().await.unwrap_or_else(|e| {
            get_global_metrics().inc_db_cleanup_failures();
            warn!("Failed to clean expired memories during key sync: {}", e);
        });
        let elapsed = cleanup_start_time.elapsed();
        get_global_metrics().record_db_cleanup_latency(elapsed.as_millis() as u64);

        Ok(KeySyncResponse { status: key_sync_response::Status::Success.into() })
    }

    async fn clean_expired_memories(&self) -> tonic::Result<()> {
        info!("Cleaning up expired memories.");
        let mut mutex_guard = self.session_context().await;
        let database =
            &mut mutex_guard.as_mut().into_failed_precondition("failed to get database")?.database;

        let num_cleaned_memories = database
            .clean_expired_memories()
            .await
            .into_internal_error("failed to clean memories")?;
        get_global_metrics().record_db_cleanup_count(num_cleaned_memories);
        Ok(())
    }

    pub async fn search_memories_handler(
        &self,
        request: SearchMemoriesRequest,
    ) -> tonic::Result<SearchMemoriesResponse> {
        let guard = self.session_context_read().await;
        let database = &guard.as_ref().into_failed_precondition("call key sync first")?.database;

        let (memories, next_page_token) =
            database.search_memories(request).await.into_internal_error("searching memories")?;
        let results =
            memories.into_iter().map(|m| SearchMemoriesResultItem { memory: Some(m) }).collect();
        Ok(SearchMemoriesResponse { results, next_page_token: next_page_token.into() })
    }

    pub async fn delete_memory_handler(
        &self,
        request: DeleteMemoryRequest,
    ) -> tonic::Result<DeleteMemoryResponse> {
        let mut mutex_guard = self.session_context().await;
        let database =
            &mut mutex_guard.as_mut().into_failed_precondition("call key sync first")?.database;

        let memory_ids: Vec<MemoryId> = request.ids.into_iter().collect();
        database
            .delete_memories(memory_ids)
            .await
            .into_internal_error("failed to delete memories")?;
        Ok(DeleteMemoryResponse { success: true, ..Default::default() })
    }

    pub async fn get_database_metrics_handler(
        &self,
        _request: GetDatabaseMetricsRequest,
    ) -> tonic::Result<GetDatabaseMetricsResponse> {
        let guard = self.session_context_read().await;
        let database = &guard.as_ref().into_failed_precondition("call key sync first")?.database;

        database.get_database_metrics().into_internal_error("failed to get database metrics")
    }

    pub async fn sync_database_handler(
        &self,
        _request: SyncDatabaseRequest,
    ) -> tonic::Result<SyncDatabaseResponse> {
        let mut mutex_guard = self.session_context().await;
        let context = mutex_guard.as_mut().into_failed_precondition("call key sync first")?;

        persistence_worker::sync_persist_database(context)
            .await
            .into_internal_error("failed to sync all memories with the persistent database")
    }
}

impl SealedMemorySessionHandler {
    pub async fn handle(&self, request_bytes: &[u8]) -> tonic::Result<Vec<u8>> {
        let request = self.deserialize_request(request_bytes).map_err(|e| {
            self.metrics.inc_requests(RequestMetricName::deserialization_failure());
            tonic::Status::internal(format!("failed to deserialize request: {e}"))
        })?;

        let request_id = request.request_id;

        let request_variant = match request.request {
            Some(v) => v,
            None => {
                let status = tonic::Status::invalid_argument("The request is empty.");
                let resp = Self::handle_error(status, self.error_propagation_behavior, request_id)?;
                return self
                    .serialize_response(&resp)
                    .into_internal_error("failed to serialize response");
            }
        };

        let metric_name = RequestMetricName::new_sealed_memory_request(&request_variant);
        self.metrics.inc_requests(metric_name.clone());

        let start_time = Instant::now();

        let result = self.handle_request_variant(request_variant).await;

        let mut response = match result {
            Ok(resp) => resp,
            Err(status) => Self::handle_error(status, self.error_propagation_behavior, request_id)?,
        };

        let elapsed_time = start_time.elapsed().as_millis() as u64;
        self.metrics.record_latency(elapsed_time, metric_name);
        response.request_id = request_id;

        self.serialize_response(&response).into_internal_error("failed to serialize response")
    }

    async fn handle_request_variant(
        &self,
        request_variant: sealed_memory_request::Request,
    ) -> tonic::Result<SealedMemoryResponse> {
        let response = match request_variant {
            sealed_memory_request::Request::UserRegistrationRequest(request) => {
                self.user_registration_handler(request).await?.into_response()
            }
            sealed_memory_request::Request::KeySyncRequest(request) => {
                self.key_sync_handler(request).await?.into_response()
            }
            sealed_memory_request::Request::AddMemoryRequest(request) => {
                self.add_memory_handler(request).await?.into_response()
            }
            #[allow(deprecated)]
            sealed_memory_request::Request::GetMemoriesRequest(request) => {
                self.get_memories_handler(request).await?.into_response()
            }
            sealed_memory_request::Request::ResetMemoryRequest(request) => {
                self.reset_memory_handler(request).await?.into_response()
            }
            sealed_memory_request::Request::GetMemoryByIdRequest(request) => {
                self.get_memory_by_id_handler(request).await?.into_response()
            }
            sealed_memory_request::Request::GetMemoryByNameRequest(request) => {
                self.get_memory_by_name_handler(request).await?.into_response()
            }
            sealed_memory_request::Request::DeleteMemoryRequest(request) => {
                self.delete_memory_handler(request).await?.into_response()
            }
            sealed_memory_request::Request::GetMemoriesByIdRequest(request) => {
                self.get_memories_by_id_handler(request).await?.into_response()
            }
            sealed_memory_request::Request::SearchMemoriesRequest(request) => {
                self.search_memories_handler(request).await?.into_response()
            }
            sealed_memory_request::Request::GetDatabaseMetricsRequest(request) => {
                self.get_database_metrics_handler(request).await?.into_response()
            }
            sealed_memory_request::Request::SyncDatabaseRequest(request) => {
                self.sync_database_handler(request).await?.into_response()
            }
        };
        Ok(response)
    }

    fn make_error_response(status: tonic::Status, request_id: i32) -> SealedMemoryResponse {
        SealedMemoryResponse {
            response: Some(sealed_memory_response::Response::Error(
                sealed_memory_rust_proto::google::rpc::Status {
                    code: status.code() as i32,
                    message: status.message().to_string(),
                    details: vec![],
                },
            )),
            request_id,
        }
    }

    fn handle_error(
        status: tonic::Status,
        error_propagation_behavior: ErrorPropagationBehavior,
        request_id: i32,
    ) -> Result<SealedMemoryResponse, tonic::Status> {
        if error_propagation_behavior == ErrorPropagationBehavior::PropagateInResponseProto {
            Ok(Self::make_error_response(status, request_id))
        } else {
            Err(status)
        }
    }
}

async fn get_or_create_db(
    db_client: &mut SealedMemoryDatabaseServiceClient<Channel>,
    uid: &BlobId,
    dek: &[u8],
    clock: Arc<dyn Clock>,
    blanket_ttl_seconds: i64,
    enable_int8_embedding: bool,
) -> tonic::Result<(IcingMetaDatabase, String, usize)> {
    let fetch_start = clock.now();
    let coarsened_expiration_timestamp =
        oak_private_memory_database::clock::calculate_coarsened_blanket_ttl(
            clock.as_ref(),
            blanket_ttl_seconds,
        );
    let metadata_blob = db_client
        .get_metadata_blob_stream(uid, coarsened_expiration_timestamp)
        .await
        .into_internal_error("Failed to get metadata blob")?;
    get_global_metrics().record_key_sync_db_fetch_latency(
        fetch_start.elapsed().unwrap_or_default().as_millis() as u64,
    );

    if let Some(EncryptedMetadataBlob { encrypted_data_blob: Some(encrypted_data_blob), version }) =
        metadata_blob
    {
        info!("Loaded database from blob: Length: {}", encrypted_data_blob.data.len());

        let decrypt_start = clock.now();
        let encrypted_info = decrypt_database(encrypted_data_blob, dek)
            .inspect_err(|_| get_global_metrics().inc_db_decryption_failures())
            .into_internal_error("failed to decrypt database")?;
        get_global_metrics().record_key_sync_decrypt_latency(
            decrypt_start.elapsed().unwrap_or_default().as_millis() as u64,
        );

        if let Some(icing_db) = encrypted_info.icing_db {
            let import_start = clock.now();
            info!("Loaded database successfully!!");
            let encoded_db = icing_db.encode_to_vec();
            let initial_size = encoded_db.len();
            let config = IcingDatabaseConfig {
                base_dir: IcingTempDir::new("sm-server-icing-"),
                enable_int8_embedding,
            };
            let db = IcingMetaDatabase::import(encoded_db.as_slice(), config)
                .into_internal_error("failed to import database")?;
            let elapsed = import_start.elapsed().unwrap_or_default();
            let db_size_bucket = metrics::bucket_db_size(initial_size);
            get_global_metrics().record_db_init_latency(elapsed.as_millis() as u64, db_size_bucket);
            return Ok((db, version, initial_size));
        }
    } else {
        debug!("no blob for {}", uid);
    }

    // This case can happen if the user is just registered, or the metadata database
    // somehow did not exist.
    // The version is empty, indicating that we can unconditionally write the
    // database.
    let config = IcingDatabaseConfig {
        base_dir: IcingTempDir::new("sm-server-icing-"),
        enable_int8_embedding,
    };
    let db = IcingMetaDatabase::new(config).into_internal_error("failed to create database")?;
    Ok((db, String::new(), 0))
}
