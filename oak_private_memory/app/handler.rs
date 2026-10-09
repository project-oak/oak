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
use std::{
    collections::{HashMap, hash_map},
    sync::Arc,
};

use encryption::{decrypt, encrypt, generate_nonce};
use external_db_client::{BlobId, DataBlobHandler};
use log::{debug, info, warn};
use metrics::RequestMetricName;
use oak_private_memory_database::{
    IcingTempDir, MemoryId,
    clock::Clock,
    database::Database,
    encryption::decrypt_database,
    icing::{DuplicateMemoryName, IcingDatabaseConfig, IcingMetaDatabase, PageToken},
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
use zeroize::Zeroizing;

use crate::{
    IntoTonicResult, admission::ActiveSessionGuard, context::UserSessionContext,
    db_client::SharedDbClient, packing::ResponsePacking, persistence_worker,
};

// The implementation for one active Oak Private Memory session.
// A new instances of this struct is created per-request.
pub struct SealedMemorySessionHandler {
    session_context: RwLock<Option<UserSessionContext>>,
    db_client: Arc<SharedDbClient>,
    metrics: Arc<metrics::Metrics>,
    persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
    clock: Arc<dyn Clock>,
    max_database_size_bytes: usize,
    blanket_ttl_seconds: i64,
    max_memory_ttl_seconds: i64,
    enable_int8_embedding: bool,
    allowed_memory_sources: Vec<String>,
    session_guard: Option<ActiveSessionGuard>,
}

impl Drop for SealedMemorySessionHandler {
    fn drop(&mut self) {
        if let Some(mut context) = self.session_context.get_mut().take() {
            if context.disable_persistence_on_close {
                info!("persistence disabled for this session, skipping");
                return;
            }
            // The context (and its Icing instance) outlives this handler while
            // it waits in the persistence queue; keep it counted until then.
            context.session_guard = self.session_guard.take();
            info!("sending session context to persistence service");
            // Count the session before sending it, so that the worker can't
            // dequeue it before it's counted. The gauge may still briefly
            // under-count if the worker reads the queue length concurrently;
            // it corrects itself at the next enqueue or pickup.
            self.metrics.inc_db_persist_queue_size();
            if let Err(e) = self.persistence_tx.send(context) {
                self.metrics.dec_db_persist_queue_size();
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
            max_database_size_bytes,
            blanket_ttl_seconds,
            max_memory_ttl_seconds,
            enable_int8_embedding,
            allowed_memory_sources,
            session_guard: None,
        }
    }

    /// Attaches the admission-control guard for this session. It is released
    /// when the handler is dropped, or, if the session is persisted on close,
    /// when the persistence worker drops the session context.
    pub fn with_session_guard(mut self, session_guard: ActiveSessionGuard) -> Self {
        self.session_guard = Some(session_guard);
        self
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

    /// Validates the memory's source.
    ///
    /// A `source` with a non-empty `source_id` is required when
    /// `memory.text_views` is non-empty or when `allowed_memory_sources` is
    /// configured. When `allowed_memory_sources` is non-empty, `source_id`
    /// must also appear in the allowlist. Returns `InvalidArgument` on failure.
    fn validate_memory_source(&self, memory: &Memory) -> tonic::Result<()> {
        if memory.text_views.as_ref().is_some_and(|tv| !tv.text_views.is_empty()) {
            let source = memory.source.as_ref().ok_or_else(|| {
                tonic::Status::invalid_argument(
                    "memory source is required when text_views is non-empty",
                )
            })?;

            if source.source_id.is_empty() {
                return Err(tonic::Status::invalid_argument("memory source_id must not be empty"));
            }
        }

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

        self.validate_single_memory(&memory, database).await?;

        let memory_id =
            database.add_memory(memory).await.into_internal_error("failed to add memory")?;
        Ok(AddMemoryResponse { id: memory_id.to_string() })
    }

    pub async fn add_memories_handler(
        &self,
        request: AddMemoriesRequest,
    ) -> tonic::Result<AddMemoriesResponse> {
        let mut mutex_guard = self.session_context().await;
        let database =
            &mut mutex_guard.as_mut().into_failed_precondition("call key sync first")?.database;

        // Pre-validate each memory; track per-item validation errors.
        let mut validated_memories: Vec<Option<Memory>> =
            Vec::with_capacity(request.memories.len());
        let mut validation_errors: Vec<Option<tonic::Status>> =
            Vec::with_capacity(request.memories.len());
        // Names claimed by earlier memories in this same batch, mapped to the
        // ID that claimed them. Nothing is written until the whole batch has
        // been validated, so `validate_single_memory` cannot see these.
        let mut claimed_names: HashMap<String, String> = HashMap::new();

        for memory in request.memories {
            let validation = match self.validate_single_memory(&memory, database).await {
                Ok(()) => Self::claim_memory_name(&memory, &mut claimed_names),
                Err(status) => Err(status),
            };
            match validation {
                Ok(()) => {
                    validated_memories.push(Some(memory));
                    validation_errors.push(None);
                }
                Err(status) => {
                    validated_memories.push(None);
                    validation_errors.push(Some(status));
                }
            }
        }

        // Collect only validated memories for the batch call.
        let batch_memories: Vec<Memory> =
            validated_memories.iter().filter_map(|m| m.clone()).collect();

        let batch_results = database.add_memories(batch_memories).await;

        // Merge validation errors and batch results into final response.
        let mut batch_iter = batch_results.into_iter();
        let mut results = Vec::with_capacity(validated_memories.len());

        for (_validated, validation_err) in validated_memories.iter().zip(validation_errors) {
            if let Some(status) = validation_err {
                results.push(Self::make_add_memory_error_result(
                    status.code() as i32,
                    status.message(),
                ));
            } else {
                // validated is Some, so batch_iter must have a result.
                let batch_result = batch_iter.next().unwrap();
                match batch_result {
                    Ok(id) => {
                        results.push(add_memories_response::AddMemoryResult {
                            result: Some(add_memories_response::add_memory_result::Result::Id(id)),
                        });
                    }
                    Err(e) => {
                        let code = Self::anyhow_to_tonic_code(&e);
                        results
                            .push(Self::make_add_memory_error_result(code as i32, &e.to_string()));
                    }
                }
            }
        }

        Ok(AddMemoriesResponse { results })
    }

    fn make_add_memory_error_result(
        code: i32,
        message: &str,
    ) -> add_memories_response::AddMemoryResult {
        add_memories_response::AddMemoryResult {
            result: Some(add_memories_response::add_memory_result::Result::Error(
                sealed_memory_rust_proto::google::rpc::Status {
                    code,
                    message: message.to_string(),
                    details: vec![],
                },
            )),
        }
    }

    /// Maps an anyhow::Error to a tonic::Code by inspecting the error chain.
    fn anyhow_to_tonic_code(err: &anyhow::Error) -> tonic::Code {
        // Try downcasting to tonic::Status first.
        if let Some(status) = err.downcast_ref::<tonic::Status>() {
            return status.code();
        }
        let msg = err.to_string().to_lowercase();
        if msg.contains("not found") {
            tonic::Code::NotFound
        } else if msg.contains("size limit exceeded") {
            tonic::Code::ResourceExhausted
        } else {
            tonic::Code::Internal
        }
    }

    /// Validates a single memory for add_memories_handler.
    async fn validate_single_memory(
        &self,
        memory: &Memory,
        database: &Database,
    ) -> Result<(), tonic::Status> {
        self.validate_memory_source(memory)?;
        self.validate_expiration_timestamp(memory.expiration_timestamp.as_ref())?;

        if !memory.id.is_empty() {
            let existing_memory =
                database.get_memory_by_id(memory.id.clone(), &None).await.map_err(|e| {
                    tonic::Status::internal(format!(
                        "failed to check for existing memory by id: {}",
                        e
                    ))
                })?;
            if existing_memory.is_none() {
                return Err(tonic::Status::not_found(format!(
                    "memory id {} was not found. Memory id may only be set for update operations, not for new memories",
                    memory.id
                )));
            }
        }

        if !memory.name.is_empty() {
            let existing_memory =
                database.get_memory_by_name(&memory.name, &None).await.map_err(|e| {
                    Self::name_lookup_status(e, "failed to check for existing named memory")
                })?;
            if let Some(existing_memory) = existing_memory
                && existing_memory.id != memory.id
            {
                return Err(tonic::Status::invalid_argument(format!(
                    "Existing memory with name {}, existing {} -> new {}",
                    memory.name, existing_memory.id, memory.id
                )));
            }
        }
        Ok(())
    }

    /// Reserves `memory`'s name for this batch, rejecting it if an earlier
    /// memory in the same batch already claimed that name.
    ///
    /// [`Self::validate_single_memory`] can only compare against memories that
    /// are already committed. Every memory in an `AddMemories` request is
    /// validated before any of them is written, so on its own that check lets a
    /// single request insert exactly the duplicates that the uniqueness rule
    /// exists to prevent.
    ///
    /// Two entries sharing a name *and* a non-empty ID are one document written
    /// twice rather than two memories competing for a name: indexing is keyed
    /// by memory ID, so the second write replaces the first and the name still
    /// resolves to a single memory. That mirrors the ID exemption in
    /// [`Self::validate_single_memory`]. An empty ID is always treated as
    /// distinct, because a fresh random ID is assigned per memory at insertion
    /// time, which would yield two documents rather than one.
    fn claim_memory_name(
        memory: &Memory,
        claimed_names: &mut HashMap<String, String>,
    ) -> Result<(), tonic::Status> {
        if memory.name.is_empty() {
            return Ok(());
        }
        match claimed_names.entry(memory.name.clone()) {
            hash_map::Entry::Occupied(claim) => {
                if memory.id.is_empty() || *claim.get() != memory.id {
                    return Err(tonic::Status::invalid_argument(format!(
                        "duplicate memory name {} in the same request, existing {} -> new {}",
                        memory.name,
                        claim.get(),
                        memory.id
                    )));
                }
                Ok(())
            }
            hash_map::Entry::Vacant(slot) => {
                slot.insert(memory.id.clone());
                Ok(())
            }
        }
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
            .map_err(|e| Self::name_lookup_status(e, "failed to get memory by name"))?;
        let success = memory.is_some();
        Ok(GetMemoryByNameResponse { memory, success })
    }

    /// Converts a name-lookup failure into a `tonic::Status`.
    ///
    /// A duplicated name is not a server fault: the database is in a state the
    /// caller has to repair, and no retry will clear it. Reporting it as
    /// `Internal` invites clients to retry forever, so it is surfaced as
    /// `FailedPrecondition` with the conflicting ids in the message. The caller
    /// can delete all but one of them — `SearchMemories` with a name filter
    /// returns the same set with full contents. Everything else stays
    /// `Internal`.
    fn name_lookup_status(err: anyhow::Error, context: &str) -> tonic::Status {
        match err.downcast_ref::<DuplicateMemoryName>() {
            Some(duplicate) => tonic::Status::failed_precondition(duplicate.to_string()),
            None => tonic::Status::internal(format!("{context}: {err:?}")),
        }
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
        dek: Zeroizing<Vec<u8>>,
        key_derivation_info: KeyDerivationInfo,
        mut db_client: SealedMemoryDatabaseServiceClient<Channel>,
        disable_persistence_on_close: bool,
    ) -> tonic::Result<()> {
        let (database, database_version, initial_size) = get_or_create_db(
            &self.metrics,
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
            // Set by `Drop` when handed to the persistence worker; while the
            // handler is alive, the handler's guard covers this context.
            session_guard: None,
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

        let key = Zeroizing::new(request.key_encryption_key);
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
            return self.decode_existing_user_registration(&uid, &data_blob);
        }

        // User does not exist.
        info!("Registering new user: {}", uid);

        // Generate a 256-bit key for the user.
        let mut dek = Zeroizing::new(vec![0u8; 32]);
        rand::rng().fill(dek.as_mut_slice());
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

        if let Err(err) = db_client
            .add_unencrypted_blob(
                DataBlob { id: uid.clone(), blob: new_plain_text_info.encode_to_vec() },
                None,
            )
            .await
        {
            // Another concurrent UserRegistration may have inserted the row
            // between our initial read and this insert-only write (returning
            // ALREADY_EXISTS, or ABORTED if the row was subsequently locked).
            // Re-read the winning row instead of failing or overwriting its DEK.
            let raced_with_another_writer = err.downcast_ref::<tonic::Status>().is_some_and(|s| {
                matches!(s.code(), tonic::Code::AlreadyExists | tonic::Code::Aborted)
            });
            if raced_with_another_writer {
                let data_blob = db_client
                    .get_unencrypted_blob(&uid, true)
                    .await
                    .into_internal_error(
                        "Failed to get unencrypted blob after concurrent registration",
                    )?
                    .into_internal_error(
                        "Unencrypted blob missing after concurrent registration",
                    )?;
                return self.decode_existing_user_registration(&uid, &data_blob);
            }
            return Err(err).into_internal_error("Failed to write blobs");
        }

        info!("Successfully registered new user {}", uid);
        // Registration deliberately does NOT establish a session context. The
        // client must call `KeySync` (which unwraps the DEK from the stored
        // blob) before issuing any memory operations. This keeps registration
        // and session establishment as separate, explicit steps.
        Ok(UserRegistrationResponse {
            status: user_registration_response::Status::Success.into(),
            key_derivation_info: Some(boot_strap_info),
        })
    }

    fn decode_existing_user_registration(
        &self,
        uid: &str,
        data_blob: &DataBlob,
    ) -> tonic::Result<UserRegistrationResponse> {
        let plain_text_info = PlainTextUserInfo::decode(&*data_blob.blob)
            .inspect_err(|_| self.metrics.inc_user_info_deserialization_failures())
            .into_internal_error("Failed to decode PlainTextUserInfo")?;
        let key_derivation_info = plain_text_info
            .key_derivation_info
            .clone()
            .into_internal_error("Empty key derivation info")?;

        info!("User have been registered!, {}", uid);
        Ok(UserRegistrationResponse {
            status: user_registration_response::Status::UserAlreadyExists.into(),
            key_derivation_info: Some(key_derivation_info),
        })
    }

    pub async fn key_sync_handler(
        &self,
        request: KeySyncRequest,
    ) -> tonic::Result<KeySyncResponse> {
        if request.key_encryption_key.is_empty() || request.pm_uid.is_empty() {
            return Ok(KeySyncResponse { status: key_sync_response::Status::InvalidPmUid.into() });
        }
        let key = Zeroizing::new(request.key_encryption_key);
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
        let dek: Zeroizing<Vec<u8>>;

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
                Zeroizing::new(dek)
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
            // TODO: b/571198870 - not covered by a metric test: cleanup only
            // fails if icing fails to delete/search, and there is no icing
            // fault-injection hook to trigger that from a test.
            self.metrics.inc_db_cleanup_failures();
            warn!("Failed to clean expired memories during key sync: {}", e);
        });
        let elapsed = cleanup_start_time.elapsed();
        self.metrics.record_db_cleanup_latency(elapsed.as_millis() as u64);

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
        self.metrics.record_db_cleanup_count(num_cleaned_memories);
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
        let not_found_ids = database
            .delete_memories(memory_ids)
            .await
            .into_internal_error("failed to delete memories")?;
        Ok(DeleteMemoryResponse { success: true, not_found_ids, ..Default::default() })
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

        persistence_worker::sync_persist_database(context, &self.metrics)
            .await
            .into_internal_error("failed to sync all memories with the persistent database")
    }
}

impl SealedMemorySessionHandler {
    /// Handles a serialized `SealedMemoryRequest` and returns the serialized
    /// `SealedMemoryResponse`.
    ///
    /// Records each failed request once in `rpc_failure_count`, so callers
    /// must not record the errors returned from here again.
    pub async fn handle(&self, request_bytes: &[u8]) -> tonic::Result<Vec<u8>> {
        let request = self.deserialize_request(request_bytes).map_err(|e| {
            let name = RequestMetricName::deserialization_failure();
            let status = tonic::Status::internal(format!("failed to deserialize request: {e}"));
            self.metrics.inc_requests(name.clone());
            self.metrics.record_failure(name, status.code());
            status
        })?;

        let request_id = request.request_id;

        let request_variant = match request.request {
            Some(v) => v,
            None => {
                let name = RequestMetricName::empty_request();
                self.metrics.inc_requests(name.clone());
                let status = tonic::Status::invalid_argument("The request is empty.");
                let code = status.code();
                let resp = Self::make_error_response(status, request_id);
                return self.serialize_and_record_outcome(name, &resp, Some(code));
            }
        };

        let metric_name = RequestMetricName::new_sealed_memory_request(&request_variant);
        self.metrics.inc_requests(metric_name.clone());

        let start_time = Instant::now();

        let result = self.handle_request_variant(request_variant).await;

        let (mut response, error_code) = match result {
            Ok(resp) => (resp, None),
            Err(status) => {
                let code = status.code();
                (Self::make_error_response(status, request_id), Some(code))
            }
        };

        let elapsed_time = start_time.elapsed().as_millis() as u64;
        self.metrics.record_latency(elapsed_time, metric_name.clone());
        response.request_id = request_id;

        self.serialize_and_record_outcome(metric_name, &response, error_code)
    }

    /// Serializes the `response` to a request counted under `name`, and
    /// records the request's failure, if any, exactly once: the serialization
    /// error if serialization fails, or else `error_code`, the code of the
    /// error that `response` carries.
    fn serialize_and_record_outcome(
        &self,
        name: RequestMetricName,
        response: &SealedMemoryResponse,
        error_code: Option<tonic::Code>,
    ) -> tonic::Result<Vec<u8>> {
        let result =
            self.serialize_response(response).into_internal_error("failed to serialize response");
        // Record the serialization error if serializing failed, otherwise the
        // error `response` carries, if any.
        if let Some(code) = result.as_ref().err().map(|status| status.code()).or(error_code) {
            self.metrics.record_failure(name, code);
        }
        result
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
            sealed_memory_request::Request::AddMemoriesRequest(request) => {
                self.add_memories_handler(request).await?.into_response()
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

    /// Wraps a failed request as a `SealedMemoryResponse` carrying the error.
    ///
    /// Every application error is reported this way: the `error` arm of the
    /// response oneof holds a `google.rpc.Status`, and the gRPC stream stays
    /// open so the session survives. Note that the oneof means the
    /// request-specific response arm is *not* populated, so a client has to
    /// check for `error` rather than inspecting a per-response success flag.
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
}

async fn get_or_create_db(
    metrics: &metrics::Metrics,
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
    let fetch_elapsed = fetch_start.elapsed().unwrap_or_default();
    metrics.record_key_sync_db_fetch_latency(fetch_elapsed.as_millis() as u64);

    if let Some(EncryptedMetadataBlob { encrypted_data_blob: Some(encrypted_data_blob), version }) =
        metadata_blob
    {
        info!("Loaded database from blob: Length: {}", encrypted_data_blob.data.len());
        metrics.record_db_load_speed(metrics::transfer_speed_kb_per_ms(
            encrypted_data_blob.encoded_len(),
            fetch_elapsed,
        ));
        metrics.record_db_size(encrypted_data_blob.data.len() as u64);

        let decrypt_start = clock.now();
        let encrypted_info = decrypt_database(encrypted_data_blob, dek)
            .inspect_err(|_| metrics.inc_db_decryption_failures())
            .into_internal_error("failed to decrypt database")?;
        metrics.record_key_sync_decrypt_latency(
            decrypt_start.elapsed().unwrap_or_default().as_millis() as u64,
        );

        if let Some(icing_db) = encrypted_info.icing_db {
            info!("Loaded database successfully!!");
            let encoded_db = icing_db.encode_to_vec();
            let initial_size = encoded_db.len();
            let config = IcingDatabaseConfig {
                base_dir: IcingTempDir::new("sm-server-icing-"),
                enable_int8_embedding,
            };
            let db = IcingMetaDatabase::import_with_metrics(encoded_db.as_slice(), config, metrics)
                .into_internal_error("failed to import database")?;
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
    let db = IcingMetaDatabase::new_with_metrics(config, metrics)
        .into_internal_error("failed to create database")?;
    let initial_db = db.export().into_internal_error("failed to export database")?;
    let initial_size = initial_db.encoded_len();
    Ok((db, String::new(), initial_size))
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{BTreeMap, BTreeSet},
        net::{IpAddr, Ipv4Addr, SocketAddr},
        sync::Arc,
        time::{Duration, SystemTime},
    };

    use metrics_testing::{Attrs, attrs};
    use oak_private_memory_database::{
        clock::{SystemClock, system_time_to_timestamp},
        database::{MAX_DATABASE_SIZE, MAX_GRPC_DECODE_SIZE},
    };
    use private_memory_test_database_server_lib::service::SealedMemoryDatabaseServiceTestImpl;
    use sealed_memory_rust_proto::oak::private_memory::SessionConfig;
    use tokio::{
        net::TcpListener,
        sync::{mpsc, oneshot},
        task::JoinHandle,
    };

    use super::*;
    use crate::{MAX_MEMORY_TTL_SECONDS, METADATA_BLANKET_TTL_SECONDS};

    /// A valid 256-bit key encryption key shared across all requests in a test.
    const TEST_KEK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";

    /// Starts an in-process test database service and returns its address.
    ///
    /// The service persists blobs in memory for the lifetime of the test, so
    /// multiple handlers ("connections") built against the same address share
    /// the same underlying storage, mirroring the real deployment where the DB
    /// is a separate long-lived service.
    async fn start_test_db() -> SocketAddr {
        let listener =
            TcpListener::bind(SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), 0)).await.unwrap();
        let db_addr = listener.local_addr().unwrap();
        tokio::spawn(async move {
            let _ = private_memory_test_database_server_lib::service::create(listener).await;
        });
        db_addr
    }

    async fn start_test_db_with_service(
        service: Arc<
            private_memory_test_database_server_lib::service::SealedMemoryDatabaseServiceTestImpl,
        >,
    ) -> SocketAddr {
        let listener =
            TcpListener::bind(SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), 0)).await.unwrap();
        let db_addr = listener.local_addr().unwrap();
        tokio::spawn(async move {
            let _ =
                private_memory_test_database_server_lib::service::serve(listener, service).await;
        });
        db_addr
    }

    /// Builds a handler ("connection") against an already-running test DB.
    ///
    /// The returned `mpsc::UnboundedReceiver` must be held for the duration of
    /// the test: dropping it would close the persistence channel that the
    /// handler sends to when a session is dropped.
    fn connect_handler(
        db_addr: SocketAddr,
    ) -> (SealedMemorySessionHandler, mpsc::UnboundedReceiver<UserSessionContext>) {
        connect_handler_with_metrics(db_addr, metrics::get_global_metrics())
    }

    /// Like [`connect_handler`], but records into `metrics`.
    fn connect_handler_with_metrics(
        db_addr: SocketAddr,
        metrics: Arc<metrics::Metrics>,
    ) -> (SealedMemorySessionHandler, mpsc::UnboundedReceiver<UserSessionContext>) {
        let (persistence_tx, persistence_rx) = mpsc::unbounded_channel();
        (connect_handler_with_persistence_tx(db_addr, metrics, persistence_tx), persistence_rx)
    }

    /// Like [`connect_handler_with_metrics`], but sends the session to
    /// `persistence_tx` when the handler is dropped.
    fn connect_handler_with_persistence_tx(
        db_addr: SocketAddr,
        metrics: Arc<metrics::Metrics>,
        persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
    ) -> SealedMemorySessionHandler {
        let db_client =
            Arc::new(SharedDbClient::new(db_addr, MAX_GRPC_DECODE_SIZE, metrics.clone()));
        SealedMemorySessionHandler::new(
            metrics,
            persistence_tx,
            db_client,
            Arc::new(SystemClock),
            MAX_DATABASE_SIZE,
            METADATA_BLANKET_TTL_SECONDS,
            MAX_MEMORY_TTL_SECONDS,
            false,
            vec![],
        )
    }

    /// Wires up a handler backed by a freshly started in-process test database
    /// service (a single "connection" against a private DB).
    async fn setup_handler()
    -> (SealedMemorySessionHandler, mpsc::UnboundedReceiver<UserSessionContext>) {
        connect_handler(start_test_db().await)
    }

    fn boot_strap_info() -> KeyDerivationInfo {
        KeyDerivationInfo { kek_salt: b"test_salt".to_vec(), kek_version: 1 }
    }

    fn registration_request(pm_uid: &str) -> UserRegistrationRequest {
        UserRegistrationRequest {
            pm_uid: pm_uid.to_string(),
            key_encryption_key: TEST_KEK.to_vec(),
            boot_strap_info: Some(boot_strap_info()),
        }
    }

    fn key_sync_request(pm_uid: &str, session_config: Option<SessionConfig>) -> KeySyncRequest {
        KeySyncRequest {
            pm_uid: pm_uid.to_string(),
            key_encryption_key: TEST_KEK.to_vec(),
            session_config,
        }
    }

    /// Registering the same `pm_uid` (with the same KEK) twice returns
    /// `UserAlreadyExists` on the second call, echoing back the stored key
    /// derivation info. Neither call establishes a session (key sync is
    /// required for that).
    #[tokio::test(flavor = "multi_thread")]
    async fn user_registration_twice_returns_already_exists() {
        let (handler, _persistence_rx) = setup_handler().await;
        let pm_uid = "registration_twice_user";
        let boot = boot_strap_info();

        // First registration creates the user but does not establish a session.
        let first = handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        assert_eq!(first.status(), user_registration_response::Status::Success);
        assert_eq!(first.key_derivation_info, Some(boot.clone()));
        assert!(handler.session_context().await.is_none());

        // Second registration reports the user already exists and returns the
        // previously stored key derivation info.
        let second = handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        assert_eq!(second.status(), user_registration_response::Status::UserAlreadyExists);
        assert_eq!(second.key_derivation_info, Some(boot));

        // Still no session after the second (early-returning) call.
        assert!(handler.session_context().await.is_none());
    }

    fn memory_expiring_in_an_hour() -> Memory {
        Memory {
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
            ..Default::default()
        }
    }

    async fn add_memory(handler: &SealedMemorySessionHandler) -> String {
        let request = AddMemoryRequest { memory: Some(memory_expiring_in_an_hour()) };
        handler.add_memory_handler(request).await.unwrap().id
    }

    async fn memory_is_readable(handler: &SealedMemorySessionHandler, id: &str) -> bool {
        let request = GetMemoryByIdRequest { id: id.to_string(), result_mask: None };
        handler.get_memory_by_id_handler(request).await.unwrap().success
    }

    async fn start_held_registration(
        service: &private_memory_test_database_server_lib::service::SealedMemoryDatabaseServiceTestImpl,
        db_addr: SocketAddr,
        pm_uid: &str,
    ) -> (JoinHandle<tonic::Result<UserRegistrationResponse>>, oneshot::Sender<()>) {
        let (arrived, release) = service.hold_next_unencrypted_write().await;
        let (handler, persistence_rx) = connect_handler(db_addr);
        let request = UserRegistrationRequest {
            pm_uid: pm_uid.to_string(),
            key_encryption_key: TEST_KEK.to_vec(),
            boot_strap_info: Some(KeyDerivationInfo {
                kek_salt: b"other_salt".to_vec(),
                kek_version: 2,
            }),
        };
        let task = tokio::spawn(async move {
            let _persistence_rx = persistence_rx;
            handler.user_registration_handler(request).await
        });
        arrived.await.expect("held registration never reached its write");
        (task, release)
    }

    /// Regression test for b/568024827. Two `UserRegistration`s for the same
    /// new user race: registration B reads "no such user", then registration
    /// A completes and its client key-syncs, adds a memory and persists it,
    /// all under A's DEK. Only then does B's write land.
    ///
    /// Before the fix, B's write overwrote A's wrapped DEK with its own, so
    /// every later KeySync unwrapped B's DEK and could not decrypt the
    /// metadata blob A had persisted: the user's memories were lost. Now B's
    /// write is refused, and B reports `UserAlreadyExists` with A's key
    /// derivation info.
    #[tokio::test(flavor = "multi_thread")]
    async fn concurrent_registration_does_not_overwrite_dek() {
        let service = Arc::new(
            private_memory_test_database_server_lib::service::SealedMemoryDatabaseServiceTestImpl::default(),
        );
        let db_addr = start_test_db_with_service(service.clone()).await;
        let pm_uid = "concurrent_registration_user";

        let (racing, release) = start_held_registration(&service, db_addr, pm_uid).await;

        let (winner, _winner_rx) = connect_handler(db_addr);
        let first = winner.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        assert_eq!(first.status(), user_registration_response::Status::Success);
        winner.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        let winner_dek = winner.session_context().await.as_ref().unwrap().dek.clone();
        let memory_id = add_memory(&winner).await;
        winner.sync_database_handler(SyncDatabaseRequest {}).await.unwrap();

        release.send(()).unwrap();
        let racing = racing.await.unwrap();

        // The user's data must still be reachable from a new connection.
        let (fresh, _fresh_rx) = connect_handler(db_addr);
        let key_sync = fresh.key_sync_handler(key_sync_request(pm_uid, None)).await;
        assert!(
            key_sync.as_ref().is_ok_and(|r| r.status() == key_sync_response::Status::Success),
            "KeySync after the concurrent registration failed: {key_sync:?}"
        );
        assert!(
            fresh.session_context().await.as_ref().unwrap().dek == winner_dek,
            "the stored DEK was replaced by the concurrent registration"
        );
        assert!(memory_is_readable(&fresh, &memory_id).await);

        let racing = racing.expect("concurrent registration failed");
        assert_eq!(racing.status(), user_registration_response::Status::UserAlreadyExists);
        assert_eq!(racing.key_derivation_info, Some(boot_strap_info()));
    }

    type TestMetrics = metrics_testing::TestMetrics<metrics::Metrics>;

    /// Returns [`metrics::Metrics`] wired to a private in-memory meter
    /// provider, so a test can read back what the code under test recorded.
    fn test_metrics() -> TestMetrics {
        TestMetrics::new(metrics::Metrics::new)
    }

    /// Returns `(count, sum)` of the histogram series `name{pairs}`.
    ///
    /// Note that `Metrics::new` records one startup sample into the `test`
    /// series of each histogram with attributes, but none into the others.
    fn histogram_count_and_sum(
        harness: &TestMetrics,
        name: &str,
        pairs: &[(&str, &str)],
    ) -> (u64, u64) {
        let snapshot = harness.collect();
        let point = snapshot.histogram(name, pairs);
        (point.count, point.sum)
    }

    /// Returns the sample count of the attribute-less histogram `name`, which
    /// is only exported once recorded (see [`histogram_count_and_sum`]).
    fn histogram_count(harness: &TestMetrics, name: &str) -> u64 {
        histogram_count_and_sum(harness, name, &[]).0
    }

    /// Returns every series of histogram `name` with its sample count, so a
    /// test can check which series a sample was recorded under and that no
    /// other series got one.
    fn histogram_series_counts(harness: &TestMetrics, name: &str) -> Vec<(Attrs, u64)> {
        harness
            .collect()
            .histogram_points(name)
            .iter()
            .map(|(series, point)| (series.clone(), point.count))
            .collect()
    }

    /// Registers and key-syncs `pm_uid` on `handler`, then adds one memory so
    /// that the session's database has changes to persist. Returns the
    /// memory's ID.
    async fn start_session_with_changes(
        handler: &SealedMemorySessionHandler,
        pm_uid: &str,
    ) -> String {
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        add_memory(handler).await
    }

    /// A sync with changes persists the database and records its size, save
    /// speed, the persist latency and the number of attempts. A sync without
    /// changes loads and rebases onto the stored database, but skips the
    /// write.
    #[tokio::test(flavor = "multi_thread")]
    async fn sync_database_records_persist_metrics() {
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(start_test_db().await, harness.metrics.clone());
        start_session_with_changes(&handler, "persist_metrics_user").await;
        // With no stored database, key sync created a new one, whose exported
        // Icing ground truth is over 100KB (`100KB-10MB`). The `test` series
        // holds the startup sample.
        assert_eq!(
            histogram_series_counts(&harness, "db_init_latency"),
            [
                (attrs(&[("db_size_bucket", "100KB-10MB")]), 1),
                (attrs(&[("db_size_bucket", "test")]), 1),
            ]
        );

        handler.sync_database_handler(SyncDatabaseRequest {}).await.unwrap();

        // The sync persisted the database on the first attempt, recording its
        // size and save speed once. There was nothing to load.
        let (count, persisted_size) = histogram_count_and_sum(&harness, "db_size", &[]);
        assert_eq!(count, 1);
        assert!(persisted_size > 0);
        assert_eq!(histogram_count(&harness, "db_persist_latency"), 1);
        assert_eq!(histogram_count(&harness, "db_persist_latency_with_retries"), 1);
        assert_eq!(histogram_count_and_sum(&harness, "db_persist_attempts", &[]), (1, 1));
        assert_eq!(histogram_count(&harness, "db_save_speed"), 1);
        assert!(!harness.collect().names().contains("db_load_speed"));

        // A second sync with no changes loads the stored database, recording
        // the load speed, and rebases onto it. The write is skipped, so it
        // isn't recorded as a persist.
        handler.sync_database_handler(SyncDatabaseRequest {}).await.unwrap();
        assert_eq!(histogram_count(&harness, "db_load_speed"), 1);
        assert_eq!(histogram_count(&harness, "db_size"), 1);
        assert_eq!(histogram_count(&harness, "db_persist_latency"), 1);
        assert_eq!(histogram_count(&harness, "db_persist_latency_with_retries"), 1);
        assert_eq!(histogram_count_and_sum(&harness, "db_persist_attempts", &[]), (1, 1));
        assert_eq!(histogram_count(&harness, "db_save_speed"), 1);
    }

    /// Returns the value of the attribute-less counter `name`.
    fn unlabeled_counter(harness: &TestMetrics, name: &str) -> u64 {
        harness.collect().counter(name, &[])
    }

    /// A key sync that finds a persisted database fetches, loads, decrypts
    /// and imports it, and records each step.
    #[tokio::test(flavor = "multi_thread")]
    async fn key_sync_of_persisted_database_records_import_metrics() {
        let db_addr = start_test_db().await;
        let pm_uid = "persisted_database_import_user";
        // The writer's metrics capture the size the database is persisted with.
        let writer_harness = test_metrics();
        let (writer, _writer_rx) =
            connect_handler_with_metrics(db_addr, writer_harness.metrics.clone());
        let memory_id = start_session_with_changes(&writer, pm_uid).await;
        writer.sync_database_handler(SyncDatabaseRequest {}).await.unwrap();
        let (_, persisted_size) = histogram_count_and_sum(&writer_harness, "db_size", &[]);

        let harness = test_metrics();
        let (reader, _reader_rx) = connect_handler_with_metrics(db_addr, harness.metrics.clone());
        let key_sync = reader.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        assert_eq!(key_sync.status(), key_sync_response::Status::Success);

        // The key sync recorded the size the database was persisted with.
        assert_eq!(histogram_count(&harness, "key_sync_db_fetch_latency"), 1);
        assert_eq!(histogram_count(&harness, "db_load_speed"), 1);
        assert_eq!(histogram_count_and_sum(&harness, "db_size", &[]), (1, persisted_size));
        assert_eq!(histogram_count(&harness, "key_sync_decrypt_latency"), 1);
        assert_eq!(unlabeled_counter(&harness, "db_decryption_failures"), 0);
        // Besides the startup sample in the `test` series, `db_init_latency`
        // has the import.
        assert_eq!(
            histogram_series_counts(&harness, "db_init_latency"),
            [
                (attrs(&[("db_size_bucket", "100KB-10MB")]), 1),
                (attrs(&[("db_size_bucket", "test")]), 1),
            ]
        );

        // Reading a memory's blob is not a load of the database.
        assert!(memory_is_readable(&reader, &memory_id).await);
        assert_eq!(histogram_count(&harness, "db_load_speed"), 1);
    }

    /// Two consecutive key syncs for a registered user (same `pm_uid` + KEK)
    /// both succeed; each one rebuilds the session context and unwraps the same
    /// stable DEK.
    #[tokio::test(flavor = "multi_thread")]
    async fn key_sync_twice_succeeds() {
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(start_test_db().await, harness.metrics.clone());
        let pm_uid = "key_sync_twice_user";

        // A wrapped DEK must exist before key sync can succeed.
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();

        let first = handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        assert_eq!(first.status(), key_sync_response::Status::Success);
        let dek_after_first = handler.session_context().await.as_ref().unwrap().dek.clone();

        let second = handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        assert_eq!(second.status(), key_sync_response::Status::Success);
        let dek_after_second = handler.session_context().await.as_ref().unwrap().dek.clone();

        // The unwrapped DEK is stable across repeated key syncs.
        assert_eq!(dek_after_first, dek_after_second);

        // Each key sync fetches the (absent) metadata blob and then cleans up
        // expired memories, of which there are none.
        assert_eq!(histogram_count(&harness, "key_sync_db_fetch_latency"), 2);
        assert_eq!(histogram_count(&harness, "db_cleanup_latency"), 2);
        assert_eq!(histogram_count_and_sum(&harness, "db_cleanup_count", &[]), (2, 0));
        // With no stored database, each key sync creates a new one, recorded
        // under its exported size bucket (`100KB-10MB`). Nothing is loaded.
        assert_eq!(
            histogram_series_counts(&harness, "db_init_latency"),
            [
                (attrs(&[("db_size_bucket", "100KB-10MB")]), 2),
                (attrs(&[("db_size_bucket", "test")]), 1),
            ]
        );
        for name in ["db_load_speed", "db_size", "key_sync_decrypt_latency"] {
            assert!(!harness.collect().names().contains(name), "{name}");
        }
    }

    /// Calling key sync twice with different `SessionConfig`s both succeed, and
    /// the most recent config wins: the session context reflects the config
    /// supplied by the latest key sync.
    #[tokio::test(flavor = "multi_thread")]
    async fn key_sync_twice_with_different_config_applies_latest() {
        let (handler, _persistence_rx) = setup_handler().await;
        let pm_uid = "key_sync_config_user";

        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();

        // First key sync keeps persistence-on-close enabled (the default).
        let first = handler
            .key_sync_handler(key_sync_request(
                pm_uid,
                Some(SessionConfig { disable_persistence_on_close: false }),
            ))
            .await
            .unwrap();
        assert_eq!(first.status(), key_sync_response::Status::Success);
        assert!(!handler.session_context().await.as_ref().unwrap().disable_persistence_on_close);

        // Second key sync flips the flag; the new config overrides the session.
        let second = handler
            .key_sync_handler(key_sync_request(
                pm_uid,
                Some(SessionConfig { disable_persistence_on_close: true }),
            ))
            .await
            .unwrap();
        assert_eq!(second.status(), key_sync_response::Status::Success);
        assert!(handler.session_context().await.as_ref().unwrap().disable_persistence_on_close);
    }

    /// Registration no longer establishes a session, so `KeySync` is mandatory
    /// before any memory operation. `add_memory` is rejected with
    /// `FailedPrecondition` after registration alone, and only succeeds once an
    /// explicit key sync has run.
    #[tokio::test(flavor = "multi_thread")]
    async fn add_memory_requires_key_sync_after_registration() {
        let (handler, _persistence_rx) = setup_handler().await;
        let pm_uid = "add_memory_requires_key_sync_user";

        let registration =
            handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        assert_eq!(registration.status(), user_registration_response::Status::Success);

        let memory = || Memory {
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
            ..Default::default()
        };

        // Registration alone leaves the session uninitialized: add_memory fails.
        let error = handler
            .add_memory_handler(AddMemoryRequest { memory: Some(memory()) })
            .await
            .unwrap_err();
        assert_eq!(error.code(), tonic::Code::FailedPrecondition);

        // After an explicit key sync, the session exists and add_memory succeeds.
        let key_sync = handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        assert_eq!(key_sync.status(), key_sync_response::Status::Success);
        let response =
            handler.add_memory_handler(AddMemoryRequest { memory: Some(memory()) }).await.unwrap();
        assert!(!response.id.is_empty());
    }

    /// The realistic flow after enforcing key sync: register on one connection,
    /// disconnect (drop the handler), then reconnect with a *new* handler and
    /// key sync. This must succeed even though registration never established a
    /// session nor persisted a metadata database blob — `get_or_create_db`
    /// creates a fresh empty database when no metadata blob exists yet.
    #[tokio::test(flavor = "multi_thread")]
    async fn key_sync_on_new_connection_after_registration_succeeds() {
        let db_addr = start_test_db().await;
        let pm_uid = "reconnect_user";

        // Connection 1: register, then drop the handler to simulate closing the
        // connection. No session was created, so nothing beyond the wrapped-DEK
        // blob is written to the DB.
        {
            let (handler, _persistence_rx) = connect_handler(db_addr);
            let registration =
                handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
            assert_eq!(registration.status(), user_registration_response::Status::Success);
            assert!(handler.session_context().await.is_none());
        }

        // Connection 2: a brand-new handler against the same DB service.
        let (handler, _persistence_rx) = connect_handler(db_addr);
        let key_sync = handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        assert_eq!(key_sync.status(), key_sync_response::Status::Success);

        // The re-established session is fully usable.
        let memory = Memory {
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
            ..Default::default()
        };
        let response =
            handler.add_memory_handler(AddMemoryRequest { memory: Some(memory) }).await.unwrap();
        assert!(!response.id.is_empty());
    }

    /// A stored `PlainTextUserInfo` that cannot be decoded fails both
    /// registration and key sync, and each failure is counted.
    #[tokio::test(flavor = "multi_thread")]
    async fn corrupt_user_info_counts_deserialization_failures() {
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(start_test_db().await, harness.metrics.clone());
        let pm_uid = "corrupt_user_info_user";
        let mut db_client = handler.db_client.get_or_connect().await.unwrap();
        db_client
            .add_unencrypted_blob(DataBlob { id: pm_uid.to_string(), blob: vec![0xFF; 4] }, None)
            .await
            .unwrap();

        let error =
            handler.user_registration_handler(registration_request(pm_uid)).await.unwrap_err();
        assert_eq!(error.code(), tonic::Code::Internal);
        assert_eq!(unlabeled_counter(&harness, "user_info_deserialization_failures"), 1);

        let error = handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap_err();
        assert_eq!(error.code(), tonic::Code::Internal);
        assert_eq!(unlabeled_counter(&harness, "user_info_deserialization_failures"), 2);
    }

    /// Length of the arbitrary ciphertext that tests store where no DEK can
    /// decrypt it, e.g. in [`store_undecryptable_metadata_blob`].
    const UNDECRYPTABLE_DATA_LEN: usize = 64;

    /// Stores a metadata blob for `pm_uid` that decodes fine but cannot be
    /// decrypted with any user's DEK, under a version no session has seen.
    async fn store_undecryptable_metadata_blob(
        service: &SealedMemoryDatabaseServiceTestImpl,
        pm_uid: &str,
    ) {
        // The ciphertext bytes are arbitrary: they won't authenticate under
        // any DEK, so decryption always fails.
        let blob =
            EncryptedDataBlob { data: vec![0xAB; UNDECRYPTABLE_DATA_LEN], nonce: generate_nonce() };
        service.metadata_database.lock().await.insert(
            pm_uid.to_string(),
            sealed_memory_rust_proto::oak::private_memory::MetadataBlob {
                data_blob: Some(DataBlob { id: pm_uid.to_string(), blob: blob.encode_to_vec() }),
                version: "undecryptable".to_string(),
            },
        );
    }

    /// A stored database that cannot be decrypted with the user's DEK fails
    /// key sync and is counted.
    #[tokio::test(flavor = "multi_thread")]
    async fn undecryptable_database_counts_decryption_failure() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let harness = test_metrics();
        let (handler, _persistence_rx) = connect_handler_with_metrics(
            start_test_db_with_service(service.clone()).await,
            harness.metrics.clone(),
        );
        let pm_uid = "undecryptable_database_user";
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        store_undecryptable_metadata_blob(&service, pm_uid).await;

        let error = handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap_err();
        assert_eq!(error.code(), tonic::Code::Internal);
        assert_eq!(unlabeled_counter(&harness, "db_decryption_failures"), 1);
        // The database was loaded, so its encrypted size and load speed are
        // recorded. The failed decryption is not timed.
        assert_eq!(
            histogram_count_and_sum(&harness, "db_size", &[]),
            (1, UNDECRYPTABLE_DATA_LEN as u64)
        );
        assert_eq!(histogram_count(&harness, "db_load_speed"), 1);
        assert!(!harness.collect().names().contains("key_sync_decrypt_latency"));
    }

    /// If the persistence worker is gone when a session ends, the session
    /// cannot be handed over for persisting, and that is counted.
    #[tokio::test(flavor = "multi_thread")]
    async fn closed_persistence_channel_counts_enqueue_failure() {
        let harness = test_metrics();
        let (handler, persistence_rx) =
            connect_handler_with_metrics(start_test_db().await, harness.metrics.clone());
        let pm_uid = "closed_persistence_channel_user";
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();

        drop(persistence_rx);
        drop(handler);

        assert_eq!(unlabeled_counter(&harness, "persistence_enqueue_failures"), 1);
        // The session was counted in the queue size before the send, and
        // uncounted when the send failed.
        assert_eq!(harness.collect().gauge("db_persist_queue_size", &[]), 0);
    }

    /// The `rpc_count` series for `request_type`.
    fn request_series(request_type: &str) -> Attrs {
        attrs(&[("request_type", request_type)])
    }

    /// The `rpc_failure_count` series for `request_type` and `status_code`.
    fn failure_series(request_type: &str, status_code: &str) -> Attrs {
        attrs(&[("request_type", request_type), ("status_code", status_code)])
    }

    /// A request that cannot be decoded fails the call, and is counted under
    /// its own request type and the total.
    #[tokio::test(flavor = "multi_thread")]
    async fn handle_counts_undecodable_request() {
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(start_test_db().await, harness.metrics.clone());
        let before = harness.collect();

        let error = handler.handle(&[0xFF; 4]).await.unwrap_err();

        assert_eq!(error.code(), tonic::Code::Internal);
        let snapshot = harness.collect();
        assert_eq!(
            snapshot.counter_increments(&before, "rpc_count"),
            BTreeMap::from([(request_series("DeserializationFailure"), 1)])
        );
        assert_eq!(
            snapshot.counter_increments(&before, "rpc_failure_count"),
            BTreeMap::from([
                (failure_series("DeserializationFailure", "INTERNAL"), 1),
                (failure_series("total", "INTERNAL"), 1),
            ])
        );
    }

    /// Handles `request`, which must fail in-band, and returns the code of the
    /// error in the response.
    async fn handle_expecting_error(
        handler: &SealedMemorySessionHandler,
        request: SealedMemoryRequest,
    ) -> tonic::Code {
        let request_id = request.request_id;
        let response = handler.handle(&request.encode_to_vec()).await.unwrap();
        let response = SealedMemoryResponse::decode(response.as_slice()).unwrap();
        assert_eq!(response.request_id, request_id);
        match response.response {
            Some(sealed_memory_response::Response::Error(status)) => tonic::Code::from(status.code),
            other => panic!("expected an error response, got {other:?}"),
        }
    }

    /// A request without a request variant gets an in-band error, and is
    /// counted under its own request type and the total.
    #[tokio::test(flavor = "multi_thread")]
    async fn handle_counts_empty_request() {
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(start_test_db().await, harness.metrics.clone());
        let before = harness.collect();

        let request = SealedMemoryRequest { request: None, request_id: 7 };
        assert_eq!(handle_expecting_error(&handler, request).await, tonic::Code::InvalidArgument);

        let snapshot = harness.collect();
        assert_eq!(
            snapshot.counter_increments(&before, "rpc_count"),
            BTreeMap::from([(request_series("EmptyRequest"), 1)])
        );
        assert_eq!(
            snapshot.counter_increments(&before, "rpc_failure_count"),
            BTreeMap::from([
                (failure_series("EmptyRequest", "INVALID_ARGUMENT"), 1),
                (failure_series("total", "INVALID_ARGUMENT"), 1),
            ])
        );
    }

    /// A failed request of any variant gets an in-band error, and is counted
    /// once under its variant and once under the total, with the error's code.
    ///
    /// A failure to serialize the response would be counted the same way, but
    /// isn't tested: encoding a response into a `Vec` cannot fail.
    #[tokio::test(flavor = "multi_thread")]
    async fn handle_counts_failed_requests_of_every_variant() {
        use sealed_memory_request::Request as RequestVariant;
        const INVALID_ARGUMENT: (tonic::Code, &str) =
            (tonic::Code::InvalidArgument, "INVALID_ARGUMENT");
        const INTERNAL: (tonic::Code, &str) = (tonic::Code::Internal, "INTERNAL");
        const FAILED_PRECONDITION: (tonic::Code, &str) =
            (tonic::Code::FailedPrecondition, "FAILED_PRECONDITION");

        let db_addr = start_test_db().await;
        // Key sync fails for a user whose stored info can't be decoded.
        let corrupt_pm_uid = "corrupt_user_info_user";
        let (handler, _persistence_rx) = connect_handler(db_addr);
        let mut db_client = handler.db_client.get_or_connect().await.unwrap();
        db_client
            .add_unencrypted_blob(
                DataBlob { id: corrupt_pm_uid.to_string(), blob: vec![0xFF; 4] },
                None,
            )
            .await
            .unwrap();

        #[allow(deprecated)]
        let cases: Vec<(&str, RequestVariant, (tonic::Code, &str))> = vec![
            // Registration requires a key encryption key.
            (
                "UserRegistrationRequest",
                RequestVariant::UserRegistrationRequest(Default::default()),
                INVALID_ARGUMENT,
            ),
            (
                "KeySyncRequest",
                RequestVariant::KeySyncRequest(key_sync_request(corrupt_pm_uid, None)),
                INTERNAL,
            ),
            // Everything else requires a key sync first.
            (
                "AddMemoryRequest",
                RequestVariant::AddMemoryRequest(Default::default()),
                FAILED_PRECONDITION,
            ),
            (
                "AddMemoriesRequest",
                RequestVariant::AddMemoriesRequest(Default::default()),
                FAILED_PRECONDITION,
            ),
            (
                "GetMemoriesRequest",
                RequestVariant::GetMemoriesRequest(Default::default()),
                FAILED_PRECONDITION,
            ),
            (
                "ResetMemoryRequest",
                RequestVariant::ResetMemoryRequest(Default::default()),
                FAILED_PRECONDITION,
            ),
            (
                "GetMemoryByIdRequest",
                RequestVariant::GetMemoryByIdRequest(Default::default()),
                FAILED_PRECONDITION,
            ),
            (
                "GetMemoryByNameRequest",
                RequestVariant::GetMemoryByNameRequest(Default::default()),
                FAILED_PRECONDITION,
            ),
            (
                "DeleteMemoryRequest",
                RequestVariant::DeleteMemoryRequest(Default::default()),
                FAILED_PRECONDITION,
            ),
            (
                "GetMemoriesByIdRequest",
                RequestVariant::GetMemoriesByIdRequest(Default::default()),
                FAILED_PRECONDITION,
            ),
            (
                "SearchMemoriesRequest",
                RequestVariant::SearchMemoriesRequest(Default::default()),
                FAILED_PRECONDITION,
            ),
            (
                "GetDatabaseMetricsRequest",
                RequestVariant::GetDatabaseMetricsRequest(Default::default()),
                FAILED_PRECONDITION,
            ),
            (
                "SyncDatabaseRequest",
                RequestVariant::SyncDatabaseRequest(Default::default()),
                FAILED_PRECONDITION,
            ),
        ];

        // The cases cover every variant: every request type that failures are
        // recorded under, other than those that aren't request variants.
        let not_variants = [
            "total",
            "Handshake",
            "DecryptionFailure",
            "DeserializationFailure",
            "EmptyRequest",
            "SessionStart",
        ];
        let variants: BTreeSet<String> = test_metrics()
            .collect()
            .counter_points("rpc_failure_count")
            .keys()
            .flatten()
            .filter(|(key, value)| key == "request_type" && !not_variants.contains(&value.as_str()))
            .map(|(_, value)| value.clone())
            .collect();
        let tested: BTreeSet<String> = cases.iter().map(|(name, _, _)| name.to_string()).collect();
        assert_eq!(tested, variants);

        for (name, request, (code, code_name)) in cases {
            let harness = test_metrics();
            let (handler, _persistence_rx) =
                connect_handler_with_metrics(db_addr, harness.metrics.clone());
            let before = harness.collect();

            let request = SealedMemoryRequest { request: Some(request), request_id: 7 };
            assert_eq!(handle_expecting_error(&handler, request).await, code, "{name}");

            let snapshot = harness.collect();
            assert_eq!(
                snapshot.counter_increments(&before, "rpc_count"),
                BTreeMap::from([(request_series(name), 1)]),
                "{name}"
            );
            assert_eq!(
                snapshot.counter_increments(&before, "rpc_failure_count"),
                BTreeMap::from([
                    (failure_series(name, code_name), 1),
                    (failure_series("total", code_name), 1)
                ]),
                "{name}"
            );
        }
    }

    /// A request that succeeds is not counted as failed, even if its response
    /// reports an unsuccessful status.
    #[tokio::test(flavor = "multi_thread")]
    async fn handle_does_not_count_successful_request_as_failed() {
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(start_test_db().await, harness.metrics.clone());
        let before = harness.collect();

        let request = SealedMemoryRequest {
            request: Some(sealed_memory_request::Request::KeySyncRequest(key_sync_request(
                "unregistered_user",
                None,
            ))),
            request_id: 7,
        };
        let response = handler.handle(&request.encode_to_vec()).await.unwrap();

        match SealedMemoryResponse::decode(response.as_slice()).unwrap().response {
            Some(sealed_memory_response::Response::KeySyncResponse(response)) => {
                assert_eq!(response.status(), key_sync_response::Status::InvalidPmUid)
            }
            other => panic!("expected a key sync response, got {other:?}"),
        }
        let snapshot = harness.collect();
        assert_eq!(
            snapshot.counter_increments(&before, "rpc_count"),
            BTreeMap::from([(request_series("KeySyncRequest"), 1)])
        );
        assert_eq!(snapshot.counter_increments(&before, "rpc_failure_count"), BTreeMap::new());
    }

    /// Enough deleted memories make a sync optimize the database first.
    #[tokio::test(flavor = "multi_thread")]
    async fn sync_database_optimizes_after_many_deletes() {
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(start_test_db().await, harness.metrics.clone());
        let pm_uid = "optimize_user";
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();

        // Optimizing needs strictly more than `OPTIMIZE_DOC_THRESHOLD` deleted
        // documents, so add and delete one more than that.
        let memories = (0..=persistence_worker::OPTIMIZE_DOC_THRESHOLD)
            .map(|_| memory_expiring_in_an_hour())
            .collect();
        let added = handler.add_memories_handler(AddMemoriesRequest { memories }).await.unwrap();
        let ids = added
            .results
            .into_iter()
            .map(|add_result| match add_result.result {
                Some(add_memories_response::add_memory_result::Result::Id(id)) => id,
                other => panic!("failed to add memory: {other:?}"),
            })
            .collect();
        handler.delete_memory_handler(DeleteMemoryRequest { ids }).await.unwrap();
        handler.sync_database_handler(SyncDatabaseRequest {}).await.unwrap();

        assert_eq!(histogram_count(&harness, "db_optimize_latency"), 1);
    }

    /// If deleting the blobs of deleted memories fails after a successful
    /// persist, the blobs that are left behind are counted.
    #[tokio::test(flavor = "multi_thread")]
    async fn sync_database_counts_orphaned_blob_deletes() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let harness = test_metrics();
        let (handler, _persistence_rx) = connect_handler_with_metrics(
            start_test_db_with_service(service.clone()).await,
            harness.metrics.clone(),
        );
        let pm_uid = "orphaned_blob_user";
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        let id = add_memory(&handler).await;
        handler.sync_database_handler(SyncDatabaseRequest {}).await.unwrap();

        handler.delete_memory_handler(DeleteMemoryRequest { ids: vec![id] }).await.unwrap();
        // Lose the memory's blob, so that the deferred blob delete fails.
        service.database.lock().await.clear();
        handler.sync_database_handler(SyncDatabaseRequest {}).await.unwrap();

        assert_eq!(unlabeled_counter(&harness, "orphaned_blob_deletes"), 1);
    }

    /// Ending a session counts it in the persist queue size as soon as it is
    /// queued, and the persistence worker records how many sessions are still
    /// queued whenever it picks one up.
    #[tokio::test(flavor = "multi_thread")]
    async fn persist_queue_size_counts_queued_sessions() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let db_addr = start_test_db_with_service(service.clone()).await;
        let harness = test_metrics();
        let queue_size = || harness.collect().gauge("db_persist_queue_size", &[]);
        let (persistence_tx, persistence_rx) = mpsc::unbounded_channel();
        for pm_uid in ["queue_size_user_1", "queue_size_user_2"] {
            let handler = connect_handler_with_persistence_tx(
                db_addr,
                harness.metrics.clone(),
                persistence_tx.clone(),
            );
            start_session_with_changes(&handler, pm_uid).await;
            drop(handler);
        }
        drop(persistence_tx);
        // Both sessions are queued before the worker runs.
        assert_eq!(queue_size(), 2);

        let (arrived, release) = service.hold_next_metadata_write().await;
        let worker = tokio::spawn(persistence_worker::run_persistence_service(
            persistence_rx,
            harness.metrics.clone(),
        ));
        tokio::time::timeout(Duration::from_secs(30), arrived)
            .await
            .expect("the persistence worker never wrote the first session")
            .unwrap();
        // The first session is being persisted and the second one is queued.
        assert_eq!(queue_size(), 1);

        release.send(()).unwrap();
        worker.await.unwrap();
        assert_eq!(queue_size(), 0);
        assert_eq!(unlabeled_counter(&harness, "db_persist_failures"), 0);
    }

    /// A session that cannot be persisted is counted by the persistence
    /// worker.
    #[tokio::test(flavor = "multi_thread")]
    async fn persistence_service_counts_persist_failures() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let harness = test_metrics();
        let (handler, _persistence_rx) = connect_handler_with_metrics(
            start_test_db_with_service(service.clone()).await,
            harness.metrics.clone(),
        );
        let pm_uid = "persist_failure_user";
        start_session_with_changes(&handler, pm_uid).await;
        // Another writer stored a database this session cannot rebase onto.
        store_undecryptable_metadata_blob(&service, pm_uid).await;

        let before = harness.collect();
        let sync = SealedMemoryRequest {
            request: Some(sealed_memory_request::Request::SyncDatabaseRequest(
                SyncDatabaseRequest {},
            )),
            request_id: 7,
        };
        assert_eq!(handle_expecting_error(&handler, sync).await, tonic::Code::Internal);
        // A failed SyncDatabase is not a lost database: the error goes back to
        // the client, and the changes stay in the session for the persistence
        // worker. So it is counted as a failed SyncDatabaseRequest, not in
        // `db_persist_failures`.
        assert_eq!(
            harness.collect().counter_increments(&before, "rpc_failure_count"),
            BTreeMap::from([
                (failure_series("SyncDatabaseRequest", "INTERNAL"), 1),
                (failure_series("total", "INTERNAL"), 1),
            ])
        );
        assert_eq!(unlabeled_counter(&harness, "db_persist_failures"), 0);
        // The sync failed to decrypt the stored database when rebasing onto it.
        assert_eq!(unlabeled_counter(&harness, "db_decryption_failures"), 1);

        let (persistence_tx, persistence_rx) = mpsc::unbounded_channel();
        persistence_tx.send(handler.session_context().await.take().unwrap()).unwrap();
        drop(persistence_tx);
        persistence_worker::run_persistence_service(persistence_rx, harness.metrics.clone()).await;

        assert_eq!(unlabeled_counter(&harness, "db_persist_failures"), 1);
        // The worker's write hit a version conflict, and it failed to decrypt
        // the stored database when rebasing onto it.
        assert_eq!(unlabeled_counter(&harness, "db_decryption_failures"), 2);
        // Nothing was persisted, so no persist (or database size) is recorded.
        for name in [
            "db_size",
            "db_save_speed",
            "db_persist_latency",
            "db_persist_latency_with_retries",
            "db_persist_attempts",
        ] {
            assert!(!harness.collect().names().contains(name), "{name}");
        }
    }

    /// A session that is persisted on close stays counted in `active_sessions`
    /// while its context waits in the persistence queue, and stops being
    /// counted only once the persistence worker drops the context.
    #[tokio::test(flavor = "multi_thread")]
    async fn session_guard_follows_context_into_persistence_queue() {
        let counter = crate::admission::SessionCounter::new(metrics::get_global_metrics());
        let (handler, mut persistence_rx) = setup_handler().await;
        let handler = handler.with_session_guard(counter.try_acquire(1).unwrap());
        assert_eq!(counter.active(), 1);

        let pm_uid = "session_guard_persist_user";
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();

        drop(handler);
        // Handler gone, but the context (and its Icing instance) is queued.
        assert_eq!(counter.active(), 1);
        let context = persistence_rx.recv().await.expect("context should be queued");
        assert!(context.session_guard.is_some());
        assert_eq!(counter.active(), 1);
        drop(context);
        assert_eq!(counter.active(), 0);
    }

    /// Without a session context (no key sync) or with persistence disabled,
    /// it stops being counted as soon as the handler is dropped.
    #[tokio::test(flavor = "multi_thread")]
    async fn session_guard_released_on_handler_drop_without_persistence() {
        let counter = crate::admission::SessionCounter::new(metrics::get_global_metrics());

        let (handler, _persistence_rx) = setup_handler().await;
        let handler = handler.with_session_guard(counter.try_acquire(1).unwrap());
        assert_eq!(counter.active(), 1);
        drop(handler);
        assert_eq!(counter.active(), 0);

        let (handler, mut persistence_rx) = setup_handler().await;
        let handler = handler.with_session_guard(counter.try_acquire(1).unwrap());
        let pm_uid = "session_guard_no_persist_user";
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler
            .key_sync_handler(key_sync_request(
                pm_uid,
                Some(SessionConfig { disable_persistence_on_close: true }),
            ))
            .await
            .unwrap();
        drop(handler);
        assert_eq!(counter.active(), 0);
        assert!(persistence_rx.try_recv().is_err());
    }

    /// A duplicated name is a state the caller has to repair, not a server
    /// fault. It must not be reported as `Internal`, which reads as "retry" and
    /// would have a client spinning forever on a condition no retry can clear.
    #[tokio::test]
    async fn duplicate_name_maps_to_failed_precondition() {
        let err = anyhow::Error::from(DuplicateMemoryName {
            name: "shared.name".to_string(),
            ids: vec!["mem_a".to_string(), "mem_b".to_string()],
        })
        .context("looking up memory by name");

        let status = SealedMemorySessionHandler::name_lookup_status(err, "unused");

        assert_eq!(status.code(), tonic::Code::FailedPrecondition);
        // The ids are the client's only handle on which memories to delete, so
        // they have to survive into the message.
        assert!(status.message().contains("mem_a"), "message was: {}", status.message());
        assert!(status.message().contains("mem_b"), "message was: {}", status.message());
        assert!(status.message().contains("shared.name"), "message was: {}", status.message());
    }

    /// Anything that is not a name conflict keeps the old behaviour, so a real
    /// infrastructure failure is not mistaken for a caller problem.
    #[tokio::test]
    async fn other_name_lookup_errors_stay_internal() {
        let err = anyhow::anyhow!("icing exploded");

        let status = SealedMemorySessionHandler::name_lookup_status(err, "getting memory by name");

        assert_eq!(status.code(), tonic::Code::Internal);
        assert!(status.message().contains("icing exploded"), "message was: {}", status.message());
    }
}
