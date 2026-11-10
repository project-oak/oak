//
// Copyright 2026 The Project Oak Authors
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

//! DEK rotation: re-encrypts all of a user's memory blobs and the metadata
//! index under a freshly generated DEK and replaces the stored wrapped DEK,
//! without losing writes from concurrent sessions. See [`rotate_dek`] for the
//! steps.

use std::{
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::Duration,
};

use external_db_client::{BlobId, DataBlobHandler, MetadataPersistResult};
use log::{error, info, warn};
use metrics::{DekRotationResponseType, DekRotationRun, Metrics};
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use sealed_memory_rust_proto::prelude::v1::*;
use tokio::time::Instant;
use tonic::{Code, transport::Channel};
use zeroize::Zeroizing;

use crate::{
    IntoTonicResult,
    context::UserSessionContext,
    dek::{Reencryption, adopt_dek, generate_wrapped_dek_blob, reencrypt_into_copies},
    persistence_worker::{
        RowLockLost, export_and_encrypt_database, persist_under_lock, rebase_onto_storage,
        write_metadata_blob,
    },
};

/// Converts the `anyhow` errors of rotation steps into a `tonic::Status` whose
/// code tells the client whether to retry.
trait IntoRotationError<T> {
    /// Fails with `message` and the [`rotation_error_code`] of the error.
    fn into_rotation_error(self, message: &str) -> tonic::Result<T>;
}

impl<T> IntoRotationError<T> for anyhow::Result<T> {
    fn into_rotation_error(self, message: &str) -> tonic::Result<T> {
        match self {
            Ok(value) => Ok(value),
            Err(error) => {
                let code = rotation_error_code(&error);
                Err(error).into_tonic_result(code, message)
            }
        }
    }
}

/// Maps [`RowLockLost`] to `ABORTED`, preserves retryable host status codes
/// (`UNAVAILABLE`, `DEADLINE_EXCEEDED`, `ABORTED`, `RESOURCE_EXHAUSTED`), and
/// maps everything else to `INTERNAL`.
fn rotation_error_code(error: &anyhow::Error) -> Code {
    if error.chain().any(|cause| cause.is::<RowLockLost>()) {
        return Code::Aborted;
    }
    error
        .chain()
        .find_map(|cause| cause.downcast_ref::<tonic::Status>())
        .map(tonic::Status::code)
        .filter(|code| {
            matches!(
                code,
                Code::Unavailable
                    | Code::DeadlineExceeded
                    | Code::Aborted
                    | Code::ResourceExhausted
            )
        })
        .unwrap_or(Code::Internal)
}

/// How long each row lock lease lasts unless [`LockTiming`] says otherwise.
const DEFAULT_LOCK_LEASE: Duration = Duration::from_secs(90);

/// How long each row lock lease lasts, how often the heartbeat renews it, and
/// how long a rotation may hold the lock in total.
#[derive(Clone, Copy, Debug)]
struct LockTiming {
    lease: Duration,
    heartbeat_interval: Duration,
    /// Kept short enough that, with the lease left behind when renewal stops,
    /// the lock is gone within the 15 minutes a background persist waits out a
    /// locked row before it gives up and drops the session's writes.
    max_hold: Duration,
}

impl Default for LockTiming {
    fn default() -> Self {
        Self {
            lease: DEFAULT_LOCK_LEASE,
            heartbeat_interval: Duration::from_secs(20),
            max_hold: Duration::from_secs(10 * 60),
        }
    }
}

/// Rotation stage named in deadline and lock-loss errors.
#[derive(Clone, Copy, Debug)]
enum RotationStep {
    CatchingUpWithStorage,
    ReencryptingMemoryBlobs,
    RepointingIndex,
    Committing,
}

impl std::fmt::Display for RotationStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            Self::CatchingUpWithStorage => "catching up with storage",
            Self::ReencryptingMemoryBlobs => "re-encrypting memory blobs",
            Self::RepointingIndex => "repointing the index",
            Self::Committing => "committing",
        };
        f.write_str(name)
    }
}

/// Renews the row lock in the background, flags the rotation aborted once the
/// lease is lost, and stops renewing once the lock has been held for
/// [`LockTiming::max_hold`].
struct HeartbeatGuard {
    task_handle: tokio::task::JoinHandle<()>,
    aborted: Arc<AtomicBool>,
    /// When the rotation must be done with the lock: [`LockTiming::max_hold`]
    /// after it was acquired.
    deadline: Instant,
}

impl HeartbeatGuard {
    /// Starts renewing the lock every `timing.heartbeat_interval`. A failed
    /// renewal is retried while at least two intervals of the lease remain. An
    /// `ABORTED` renewal, running out of lease, or reaching `timing.max_hold`
    /// stops the renewals and marks the rotation aborted.
    fn spawn(
        uid: String,
        lock_token: String,
        mut db_client: SealedMemoryDatabaseServiceClient<Channel>,
        metrics: Arc<Metrics>,
        timing: LockTiming,
    ) -> Self {
        let aborted = Arc::new(AtomicBool::new(false));
        let aborted_clone = aborted.clone();
        let hold_deadline = Instant::now() + timing.max_hold;

        let task_handle = tokio::spawn(async move {
            let mut interval = tokio::time::interval(timing.heartbeat_interval);
            // The first tick completes immediately; skip it so the first renewal
            // comes one interval after the lock was acquired.
            interval.tick().await;
            let mut last_renewed = Instant::now();
            loop {
                interval.tick().await;
                if Instant::now() >= hold_deadline {
                    error!(
                        "Held the row lock for user {uid} for {:?}; aborting rotation",
                        timing.max_hold
                    );
                    aborted_clone.store(true, Ordering::SeqCst);
                    break;
                }
                let extend =
                    db_client.extend_unencrypted_blob_lock(&uid, &lock_token, timing.lease);
                let outcome = tokio::time::timeout(timing.heartbeat_interval, extend)
                    .await
                    .unwrap_or_else(|_| Err(anyhow::anyhow!("lock extension timed out")));
                let Err(e) = outcome else {
                    last_renewed = Instant::now();
                    continue;
                };
                let lease_revoked = e
                    .downcast_ref::<tonic::Status>()
                    .is_some_and(|status| status.code() == Code::Aborted);
                let lease_has_room =
                    last_renewed.elapsed() + 2 * timing.heartbeat_interval < timing.lease;
                if !lease_revoked && lease_has_room {
                    warn!("Failed to renew row lock for user {uid}, will retry: {e:?}");
                    continue;
                }
                error!("Lost row lock for user {uid}: {e:?}; aborting rotation");
                metrics.inc_dek_rotation_lock_extend_failures();
                aborted_clone.store(true, Ordering::SeqCst);
                break;
            }
        });

        Self { task_handle, aborted, deadline: hold_deadline }
    }

    /// Fails if the rotation must stop before `step`: with `DEADLINE_EXCEEDED`
    /// once the lock has been held for [`LockTiming::max_hold`], or with
    /// `ABORTED` if the lock was lost.
    fn check(&self, step: RotationStep) -> tonic::Result<()> {
        // Checked first: at the deadline the heartbeat also sets `aborted`.
        if Instant::now() >= self.deadline {
            return Err(tonic::Status::deadline_exceeded(format!(
                "row lock held for the maximum time before {step}"
            )));
        }
        if self.aborted.load(Ordering::SeqCst) {
            return Err(tonic::Status::aborted(format!("row lock lost before {step}")));
        }
        Ok(())
    }
}

/// Awaits `future` until the heartbeat's deadline and fails with
/// `DEADLINE_EXCEEDED`, naming `step`, if it takes longer, so a stuck host RPC
/// doesn't keep the rotation running after the heartbeat stops renewing the
/// lock.
async fn before_deadline<T>(
    heartbeat: &HeartbeatGuard,
    step: RotationStep,
    future: impl Future<Output = tonic::Result<T>>,
) -> tonic::Result<T> {
    tokio::time::timeout_at(heartbeat.deadline, future).await.unwrap_or_else(|_| {
        Err(tonic::Status::deadline_exceeded(format!(
            "row lock held for the maximum time while {step}"
        )))
    })
}

impl Drop for HeartbeatGuard {
    fn drop(&mut self) {
        self.task_handle.abort();
    }
}

/// Releases the row lock on drop if [`RowLockGuard::release`] was not called
/// (e.g. if the RPC was cancelled).
struct RowLockGuard {
    uid: String,
    lock_token: String,
    db_client: Option<SealedMemoryDatabaseServiceClient<Channel>>,
}

impl RowLockGuard {
    fn new(
        uid: String,
        lock_token: String,
        db_client: SealedMemoryDatabaseServiceClient<Channel>,
    ) -> Self {
        Self { uid, lock_token, db_client: Some(db_client) }
    }

    async fn release(mut self) {
        if let Some(db_client) = self.db_client.take() {
            release_row_lock(db_client, &self.uid, &self.lock_token).await;
        }
    }
}

impl Drop for RowLockGuard {
    fn drop(&mut self) {
        let Some(db_client) = self.db_client.take() else { return };
        let uid = std::mem::take(&mut self.uid);
        let lock_token = std::mem::take(&mut self.lock_token);
        match tokio::runtime::Handle::try_current() {
            Ok(runtime) => {
                runtime.spawn(async move { release_row_lock(db_client, &uid, &lock_token).await });
            }
            Err(_) => warn!("No runtime to release the row lock for user {uid}; it expires"),
        }
    }
}

async fn release_row_lock(
    mut db_client: SealedMemoryDatabaseServiceClient<Channel>,
    uid: &BlobId,
    lock_token: &str,
) {
    if let Err(e) = db_client.release_unencrypted_blob_lock(uid, lock_token).await {
        warn!("Failed to release row lock: {e:?}");
    }
}

/// Acquires the exclusive lock on the user's `UnencryptedDataBlobs` row for
/// `timing.lease` and starts a [`HeartbeatGuard`] that keeps renewing it. Fails
/// with `ABORTED` if another writer holds the lock. Returns the lock token,
/// which the rotation presents on its metadata writes: while the lease holds,
/// other writers can't commit, and the metadata version check catches any
/// write that lands after it lapses.
async fn acquire_row_lock(
    user_context: &mut UserSessionContext,
    metrics: &Arc<Metrics>,
    timing: LockTiming,
) -> tonic::Result<(String, HeartbeatGuard)> {
    let lock = user_context
        .database_service_client
        .acquire_unencrypted_blob_lock(&user_context.uid, timing.lease)
        .await
        .into_rotation_error("failed to acquire row lock")?;

    info!("Acquired row lock for user {}", user_context.uid);
    let heartbeat = HeartbeatGuard::spawn(
        user_context.uid.clone(),
        lock.lock_token.clone(),
        user_context.database_service_client.clone(),
        metrics.clone(),
        timing,
    );
    Ok((lock.lock_token, heartbeat))
}

/// Brings the session up to date with storage under the lock: rebases onto the
/// latest stored metadata blob, purges expired memories so their blobs aren't
/// re-encrypted, and persists pending changes with `lock_token`. Afterwards the
/// session's index matches storage, so every live memory blob gets
/// re-encrypted and the commit's version check passes.
async fn catch_up_with_storage(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
    lock_token: &str,
) -> tonic::Result<()> {
    rebase_onto_storage(user_context, metrics)
        .await
        .into_rotation_error("failed to rebase onto storage")?;
    let cleanup_start_time = Instant::now();
    let purged = user_context
        .database
        .clean_expired_memories()
        .await
        .into_rotation_error("failed to purge expired memories")?;
    metrics.record_db_cleanup_latency(cleanup_start_time.elapsed().as_millis() as u64);
    metrics.record_db_cleanup_count(purged);
    if purged > 0 {
        info!("Purged {purged} expired memories before rotating");
    }
    persist_under_lock(user_context, metrics, lock_token)
        .await
        .into_rotation_error("failed to persist pending changes under the lock")
}

/// Copies every memory blob in the index into a new blob encrypted under
/// `DEK_new`, checking the heartbeat before each batch. If any batch fails or
/// the heartbeat aborts, [`reencrypt_into_copies`] calls
/// [`Reencryption::discard`], which sends a `DeleteBlobs` RPC to the host to
/// soft-delete the copy blobs written by earlier batches (marking their rows
/// deleted in Spanner so they are garbage-collected after TTL).
async fn reencrypt_all_memory_blobs(
    user_context: &mut UserSessionContext,
    dek_new: &[u8],
    heartbeat: &HeartbeatGuard,
) -> tonic::Result<Reencryption> {
    let old_blobs = user_context
        .database
        .get_all_memory_and_blob_ids()
        .into_internal_error("failed to list memories")?;
    let reencryption =
        reencrypt_into_copies(&mut user_context.database, &old_blobs, dek_new, || {
            heartbeat.check(RotationStep::ReencryptingMemoryBlobs).map_err(anyhow::Error::from)
        })
        .await
        .into_rotation_error("failed to re-encrypt memory blobs")?;
    for (memory_id, blob_id) in &reencryption.missing {
        warn!("Memory {memory_id} has no blob {blob_id}; not re-encrypting it");
    }
    Ok(reencryption)
}

/// Points the session's index at the re-encrypted copies, then exports and
/// encrypts the index under `DEK_new`.
fn repoint_and_export_metadata(
    user_context: &mut UserSessionContext,
    dek_new: &[u8],
    reencryption: &Reencryption,
    heartbeat: &HeartbeatGuard,
) -> tonic::Result<EncryptedDataBlob> {
    heartbeat.check(RotationStep::RepointingIndex)?;
    if user_context.database.changed() {
        return Err(tonic::Status::internal("unpersisted changes before repointing the index"));
    }
    reencryption
        .repoint(&mut user_context.database)
        .into_internal_error("failed to repoint index")?;
    export_and_encrypt_database(&user_context.database, dek_new)
        .into_internal_error("failed to encrypt metadata")
}

/// Writes the new metadata blob and the wrapped `DEK_new` in a single host
/// transaction fenced by `lock_token`.
async fn commit_rotation(
    user_context: &mut UserSessionContext,
    lock_token: &str,
    metadata_blob_new: EncryptedDataBlob,
    unencrypted_data_blob_new: DataBlob,
    heartbeat: &HeartbeatGuard,
) -> tonic::Result<Option<String>> {
    heartbeat.check(RotationStep::Committing)?;
    let metadata_blob = EncryptedMetadataBlob {
        encrypted_data_blob: Some(metadata_blob_new),
        version: user_context.database_version.clone(),
    };
    let commit = async {
        write_metadata_blob(
            user_context,
            &metadata_blob,
            lock_token,
            Some(unencrypted_data_blob_new),
        )
        .await
        .into_rotation_error("atomic commit RPC failed")
    };
    match before_deadline(heartbeat, RotationStep::Committing, commit).await? {
        MetadataPersistResult::Succeeded { committed_version } => Ok(committed_version),
        MetadataPersistResult::RetryNeeded => {
            Err(tonic::Status::aborted("version conflict during rotation commit"))
        }
        MetadataPersistResult::LockConflict => {
            Err(tonic::Status::aborted("row lock lapsed before rotation commit"))
        }
    }
}

/// Points the index back at the `DEK_old` blobs and soft-deletes the copies.
/// Returns `status`, or `DATA_LOSS` if the index cannot be restored.
async fn roll_back(
    user_context: &mut UserSessionContext,
    reencryption: &Reencryption,
    status: tonic::Status,
) -> tonic::Status {
    let restored = reencryption.undo_repoint(&mut user_context.database);
    reencryption.discard(&mut user_context.database).await;
    if let Err(e) = restored {
        error!("Failed to roll back index after aborted DEK rotation: {e:?}");
        return tonic::Status::data_loss(
            "DEK rotation failed and the session could not be restored; it must be discarded",
        );
    }
    status
}

/// Repoints the index at the copies and commits the new metadata blob and
/// wrapped DEK, rolling back the index and discarding the copies on failure.
async fn commit_or_roll_back(
    user_context: &mut UserSessionContext,
    lock_token: &str,
    dek_new: &[u8],
    unencrypted_data_blob_new: DataBlob,
    reencryption: &Reencryption,
    heartbeat: &HeartbeatGuard,
) -> tonic::Result<()> {
    let metadata_blob_new =
        match repoint_and_export_metadata(user_context, dek_new, reencryption, heartbeat) {
            Ok(metadata_blob_new) => metadata_blob_new,
            Err(status) => {
                return Err(roll_back(user_context, reencryption, status).await);
            }
        };
    match commit_rotation(
        user_context,
        lock_token,
        metadata_blob_new,
        unencrypted_data_blob_new,
        heartbeat,
    )
    .await
    {
        Ok(committed_version) => {
            if let Some(committed_version) = committed_version {
                user_context.database_version = committed_version;
            }
            Ok(())
        }
        Err(status) => Err(roll_back(user_context, reencryption, status).await),
    }
}

/// Switches the session to `DEK_new` and soft-deletes the superseded `DEK_old`
/// blobs (the host keeps soft-deleted blobs readable for an hour so other live
/// sessions have time to sync).
async fn finish_rotation(
    user_context: &mut UserSessionContext,
    dek_new: Zeroizing<Vec<u8>>,
    reencryption: Reencryption,
) {
    adopt_dek(user_context, dek_new, &reencryption.superseded()).await;
}

/// Maps a rotation result to the `response_type` label of `dek_rotation_count`.
fn response_type<T>(result: &tonic::Result<T>) -> DekRotationResponseType {
    let Err(status) = result else {
        return DekRotationResponseType::Ok;
    };
    match status.code() {
        Code::Aborted | Code::Unavailable | Code::DeadlineExceeded | Code::ResourceExhausted => {
            DekRotationResponseType::RetryError
        }
        Code::Unauthenticated | Code::FailedPrecondition => {
            DekRotationResponseType::Unauthenticated
        }
        Code::InvalidArgument => DekRotationResponseType::InvalidArgument,
        _ => DekRotationResponseType::InternalError,
    }
}

/// Rotates the DEK of the session's user and records the rotation metrics.
/// Fails with `FAILED_PRECONDITION` if there is no session yet (no KeySync).
///
/// The rotation holds the user's `UnencryptedDataBlobs` row lock throughout, so
/// other sessions' writes wait (or fail with `ABORTED`) until it finishes:
/// 1. [`acquire_row_lock`] takes the lock and starts the heartbeat that renews
///    it, for at most [`LockTiming::max_hold`].
/// 2. [`catch_up_with_storage`] rebases, purges expired memories and persists
///    pending changes, so the index matches storage.
/// 3. [`generate_wrapped_dek_blob`] generates `DEK_new` and wraps it under the
///    session KEK.
/// 4. [`reencrypt_all_memory_blobs`] copies every memory blob under `DEK_new`.
/// 5. [`commit_or_roll_back`] repoints the index at the copies and commits the
///    new metadata blob and wrapped DEK together, or undoes the repoint.
/// 6. [`finish_rotation`] switches the session to `DEK_new` and soft-deletes
///    the old blobs.
///
/// The lock is released on every path, including cancellation. If the rotation
/// fails, the session and storage keep working under `DEK_old`. Returns
/// `DATA_LOSS` if a failed commit could not be rolled back; the session must
/// then be discarded without persisting it.
pub(crate) async fn rotate_dek(
    user_context: Option<&mut UserSessionContext>,
    metrics: &Arc<Metrics>,
) -> tonic::Result<RotateDekResponse> {
    rotate_dek_with_timing(user_context, metrics, LockTiming::default()).await
}

/// Runs [`rotate_dek`] with custom [`LockTiming`] and records rotation metrics.
async fn rotate_dek_with_timing(
    user_context: Option<&mut UserSessionContext>,
    metrics: &Arc<Metrics>,
    timing: LockTiming,
) -> tonic::Result<RotateDekResponse> {
    let start_time = Instant::now();
    let result = match user_context {
        Some(user_context) => run_rotation(user_context, metrics, timing).await,
        None => Err(tonic::Status::failed_precondition("call key sync first")),
    };

    metrics.inc_dek_rotation_count(response_type(&result));
    let run = match &result {
        Ok(response) => DekRotationRun::Succeeded {
            blobs: response.reencrypted_memories_count as u64,
            ciphertext_bytes: response.reencrypted_bytes as u64,
        },
        Err(_) => DekRotationRun::Failed,
    };
    metrics.record_dek_rotation_run(run, start_time.elapsed().as_millis() as u64);
    result
}

/// Runs the steps listed on [`rotate_dek`] with the given lock timing.
async fn run_rotation(
    user_context: &mut UserSessionContext,
    metrics: &Arc<Metrics>,
    timing: LockTiming,
) -> tonic::Result<RotateDekResponse> {
    if user_context.disable_persistence_on_close && user_context.database.changed() {
        return Err(tonic::Status::failed_precondition(
            "the session has unsynced changes; call SyncDatabase before RotateDek",
        ));
    }
    info!("Starting DEK rotation for user {}", user_context.uid);

    let (lock_token, heartbeat) = acquire_row_lock(user_context, metrics, timing).await?;
    let row_lock = RowLockGuard::new(
        user_context.uid.clone(),
        lock_token.clone(),
        user_context.database_service_client.clone(),
    );

    let result = async {
        let catch_up = catch_up_with_storage(user_context, metrics, &lock_token);
        before_deadline(&heartbeat, RotationStep::CatchingUpWithStorage, catch_up).await?;
        let (dek_new, unencrypted_blob_new) = generate_wrapped_dek_blob(
            &user_context.uid,
            &user_context.kek,
            user_context.database.key_derivation_info().clone(),
        )
        .into_internal_error("failed to wrap new DEK")?;
        let reencryption = reencrypt_all_memory_blobs(user_context, &dek_new, &heartbeat).await?;
        commit_or_roll_back(
            user_context,
            &lock_token,
            &dek_new,
            unencrypted_blob_new,
            &reencryption,
            &heartbeat,
        )
        .await?;
        info!(
            "Committed DEK rotation for user {} ({} memories, {} missing blobs)",
            user_context.uid,
            reencryption.repoints.len(),
            reencryption.missing.len()
        );

        let response = RotateDekResponse {
            reencrypted_memories_count: reencryption.repoints.len() as i64,
            reencrypted_bytes: reencryption.ciphertext_bytes as i64,
        };
        finish_rotation(user_context, dek_new, reencryption).await;
        Ok(response)
    }
    .await;

    drop(heartbeat);
    row_lock.release().await;
    result
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, net::SocketAddr, time::SystemTime};

    use oak_private_memory_database::{MemoryId, clock::system_time_to_timestamp};
    use private_memory_test_database_server_lib::service::{
        CLOCK_SKEW_MARGIN, SealedMemoryDatabaseServiceTestImpl,
    };
    use prost::Message;
    use sealed_memory_rust_proto::oak::private_memory::{Memory, SessionConfig};
    use tokio::sync::mpsc;

    use super::*;
    use crate::{
        dek::{FAIL_UNDO_REPOINT, extract_and_unwrap_dek},
        handler::SealedMemorySessionHandler,
        persistence_worker::sync_persist_database,
        test_util::{
            add_tagged, connect_handler, connect_handler_with_metrics, key_sync_request,
            registration_request, sorted_stored_blob_ids, start_test_db_with_service, tags_of,
        },
    };

    type TestMetrics = metrics_testing::TestMetrics<Metrics>;

    struct Setup {
        service: Arc<SealedMemoryDatabaseServiceTestImpl>,
        db_addr: SocketAddr,
        handler: SealedMemorySessionHandler,
        harness: TestMetrics,
        _persistence_rx: mpsc::UnboundedReceiver<UserSessionContext>,
    }

    async fn setup(pm_uid: &str) -> Setup {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let db_addr = start_test_db_with_service(service.clone()).await;
        let harness = TestMetrics::new(Metrics::new);
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        Setup { service, db_addr, handler, harness, _persistence_rx }
    }

    fn memory_expiring_at(tag: &str, expiration: SystemTime) -> Memory {
        Memory {
            tags: vec![tag.to_string()],
            expiration_timestamp: Some(system_time_to_timestamp(expiration)),
            ..Default::default()
        }
    }

    async fn assert_fresh_session_reads(
        db_addr: SocketAddr,
        pm_uid: &str,
        memories: &[(String, &str)],
    ) {
        let (reader, _persistence_rx) = connect_handler(db_addr);
        reader.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        for (id, tag) in memories {
            assert_eq!(tags_of(&reader, id).await, Some(vec![tag.to_string()]), "memory {id}");
        }
    }

    fn rotation_latency_count(harness: &TestMetrics, pairs: &[(&str, &str)]) -> u64 {
        harness.collect().histogram("dek_rotation_latency_ms", pairs).count
    }

    async fn stored_dek(
        service: &SealedMemoryDatabaseServiceTestImpl,
        pm_uid: &str,
        kek: &[u8],
    ) -> Zeroizing<Vec<u8>> {
        let blob = service.unencrypted_database.lock().await.get(pm_uid).cloned().unwrap();
        extract_and_unwrap_dek(&PlainTextUserInfo::decode(&*blob.blob).unwrap(), kek).unwrap()
    }

    fn sorted_blob_ids(ctx: &UserSessionContext) -> Vec<(MemoryId, BlobId)> {
        let mut ids = ctx.database.get_all_memory_and_blob_ids().unwrap();
        ids.sort();
        ids
    }

    async fn wait_for_abort(guard: &HeartbeatGuard, timeout: Duration) {
        let deadline = Instant::now() + timeout;
        while guard.check(RotationStep::Committing).is_ok() {
            assert!(Instant::now() < deadline, "heartbeat did not abort within {timeout:?}");
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    }

    async fn wait_for_lock_release(service: &SealedMemoryDatabaseServiceTestImpl, pm_uid: &str) {
        let deadline = Instant::now() + Duration::from_secs(10);
        while service.lock_state.held_token(pm_uid).await.is_some() {
            assert!(Instant::now() < deadline, "row lock was not released");
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    }

    /// A rotation must give the row back while background persists are still
    /// waiting it out, or they drop their sessions' writes.
    #[test]
    fn lock_is_gone_before_background_persists_give_up() {
        let timing = LockTiming::default();
        // Storage keeps a lapsed lock for a few more seconds of clock skew.
        let skew_margin = Duration::from_secs(5);
        assert!(
            timing.max_hold + timing.lease + skew_margin
                < crate::persistence_worker::BACKGROUND_LOCK_WAIT
        );
    }

    #[test]
    fn into_rotation_error_preserves_only_retryable_host_codes() {
        let code =
            |result: anyhow::Result<()>| result.into_rotation_error("test").unwrap_err().code();
        for retryable in
            [Code::Unavailable, Code::DeadlineExceeded, Code::Aborted, Code::ResourceExhausted]
        {
            let status = tonic::Status::new(retryable, "host");
            assert_eq!(code(Err(anyhow::Error::from(status).context("rpc"))), retryable);
        }
        assert_eq!(
            code(Err(anyhow::Error::from(RowLockLost).context("persisting"))),
            Code::Aborted
        );
        assert_eq!(code(Err(tonic::Status::not_found("host").into())), Code::Internal);
        assert_eq!(code(Err(anyhow::anyhow!("local failure"))), Code::Internal);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn acquire_row_lock_fails_with_aborted_while_another_session_holds_it() {
        let pm_uid = "contended_lock_user";
        let Setup { service, db_addr, handler, harness, _persistence_rx: _rx } =
            setup(pm_uid).await;
        let (other, _other_rx) = connect_handler(db_addr);
        other.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        let timing = LockTiming::default();
        let mut guard = handler.session_context().await;
        let (token, _heartbeat) =
            acquire_row_lock(guard.as_mut().unwrap(), &harness.metrics, timing).await.unwrap();

        let mut other_guard = other.session_context().await;
        let result =
            acquire_row_lock(other_guard.as_mut().unwrap(), &harness.metrics, timing).await;

        assert_eq!(result.err().unwrap().code(), Code::Aborted);
        assert_eq!(service.lock_state.held_token(pm_uid).await, Some(token));
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn row_lock_guard_release_frees_the_lock() {
        let pm_uid = "release_lock_user";
        let Setup { service, handler, harness, _persistence_rx: _rx, .. } = setup(pm_uid).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let (token, heartbeat) =
            acquire_row_lock(ctx, &harness.metrics, LockTiming::default()).await.unwrap();
        drop(heartbeat);
        let row_lock =
            RowLockGuard::new(ctx.uid.clone(), token, ctx.database_service_client.clone());

        row_lock.release().await;

        assert_eq!(service.lock_state.held_token(pm_uid).await, None);
        acquire_row_lock(ctx, &harness.metrics, LockTiming::default()).await.unwrap();
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn dropped_row_lock_guard_frees_the_lock() {
        let pm_uid = "dropped_lock_user";
        let Setup { service, handler, harness, _persistence_rx: _rx, .. } = setup(pm_uid).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let (token, heartbeat) =
            acquire_row_lock(ctx, &harness.metrics, LockTiming::default()).await.unwrap();
        drop(heartbeat);
        let row_lock =
            RowLockGuard::new(ctx.uid.clone(), token, ctx.database_service_client.clone());

        drop(row_lock);

        wait_for_lock_release(&service, pm_uid).await;
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn heartbeat_aborts_once_the_lease_is_lost() {
        let pm_uid = "heartbeat_lost_user";
        let Setup { service, handler, harness, _persistence_rx: _rx, .. } = setup(pm_uid).await;
        let timing = LockTiming {
            lease: Duration::from_secs(60),
            heartbeat_interval: Duration::from_millis(10),
            ..LockTiming::default()
        };
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let (_token, heartbeat) = acquire_row_lock(ctx, &harness.metrics, timing).await.unwrap();

        tokio::time::sleep(Duration::from_millis(100)).await;
        assert!(heartbeat.check(RotationStep::Committing).is_ok());
        assert_eq!(harness.collect().counter("dek_rotation_lock_extend_failures", &[]), 0);

        service.lock_state.advance(timing.lease + Duration::from_secs(1));
        wait_for_abort(&heartbeat, Duration::from_secs(10)).await;
        assert_eq!(heartbeat.check(RotationStep::Committing).unwrap_err().code(), Code::Aborted);
        assert_eq!(harness.collect().counter("dek_rotation_lock_extend_failures", &[]), 1);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn heartbeat_aborts_once_the_lock_is_held_for_max_hold() {
        let pm_uid = "max_hold_user";
        let Setup { service, handler, harness, _persistence_rx: _rx, .. } = setup(pm_uid).await;
        let timing = LockTiming {
            heartbeat_interval: Duration::from_millis(10),
            max_hold: Duration::from_millis(200),
            ..LockTiming::default()
        };
        let mut guard = handler.session_context().await;
        let started = Instant::now();
        let (token, heartbeat) =
            acquire_row_lock(guard.as_mut().unwrap(), &harness.metrics, timing).await.unwrap();

        wait_for_abort(&heartbeat, Duration::from_secs(10)).await;

        assert!(started.elapsed() >= timing.max_hold);
        assert_eq!(
            heartbeat.check(RotationStep::Committing).unwrap_err().code(),
            Code::DeadlineExceeded
        );
        assert_eq!(harness.collect().counter("dek_rotation_lock_extend_failures", &[]), 0);
        // The lease itself is still held; the rotation releases it.
        assert_eq!(service.lock_state.held_token(pm_uid).await, Some(token));
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn heartbeat_retries_failed_renewals_while_the_lease_allows() {
        let Setup { handler, harness, _persistence_rx: _rx, .. } =
            setup("heartbeat_retry_user").await;
        let timing = LockTiming {
            lease: Duration::from_secs(3),
            heartbeat_interval: Duration::from_millis(200),
            ..LockTiming::default()
        };
        let guard = handler.session_context().await;
        let ctx = guard.as_ref().unwrap();
        let started = Instant::now();
        let heartbeat = HeartbeatGuard::spawn(
            ctx.uid.clone(),
            String::new(),
            ctx.database_service_client.clone(),
            harness.metrics.clone(),
            timing,
        );

        tokio::time::sleep(Duration::from_secs(1)).await;
        assert!(
            heartbeat.check(RotationStep::Committing).is_ok(),
            "gave up while the lease had room"
        );
        assert_eq!(harness.collect().counter("dek_rotation_lock_extend_failures", &[]), 0);
        wait_for_abort(&heartbeat, Duration::from_secs(10)).await;
        assert!(started.elapsed() >= timing.lease - 2 * timing.heartbeat_interval);
        assert_eq!(harness.collect().counter("dek_rotation_lock_extend_failures", &[]), 1);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn catch_up_with_storage_rebases_purges_and_persists_under_the_lock() {
        let pm_uid = "catch_up_user";
        let Setup { service, db_addr, handler, harness, _persistence_rx: _rx } =
            setup(pm_uid).await;
        let expired = {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            let expired = ctx
                .database
                .add_memory(memory_expiring_at(
                    "expired",
                    SystemTime::now() - Duration::from_secs(60),
                ))
                .await
                .unwrap();
            sync_persist_database(ctx, &harness.metrics).await.unwrap();
            expired
        };
        let (writer, _writer_rx) = connect_handler(db_addr);
        writer.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        let remote = add_tagged(&writer, "remote").await;
        sync_persist_database(writer.session_context().await.as_mut().unwrap(), &harness.metrics)
            .await
            .unwrap();
        let pending = add_tagged(&handler, "pending").await;

        {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            let (token, _heartbeat) =
                acquire_row_lock(ctx, &harness.metrics, LockTiming::default()).await.unwrap();

            catch_up_with_storage(ctx, &harness.metrics, &token).await.unwrap();

            assert!(!ctx.database.changed());
            let stored_version = service.metadata_database.lock().await[pm_uid].version.clone();
            assert_eq!(ctx.database_version, stored_version);
            let ids = ctx.database.get_all_memory_and_blob_ids().unwrap();
            assert!(ids.iter().all(|(memory_id, _)| *memory_id != expired), "expired kept");
            assert_eq!(service.lock_state.held_token(pm_uid).await, Some(token));
        }
        assert_fresh_session_reads(db_addr, pm_uid, &[(remote, "remote"), (pending, "pending")])
            .await;
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn rotate_dek_without_a_session_is_a_failed_precondition() {
        let harness = TestMetrics::new(Metrics::new);

        let status = rotate_dek(None, &harness.metrics).await.unwrap_err();

        assert_eq!(status.code(), Code::FailedPrecondition);
        assert_eq!(
            harness
                .collect()
                .counter("dek_rotation_count", &[("response_type", "unauthenticated")]),
            1
        );
        assert_eq!(
            rotation_latency_count(
                &harness,
                &[("status", "failure"), ("bytes_tier", "unknown"), ("blobs_tier", "unknown")]
            ),
            1
        );
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn rotation_rejects_unsynced_changes_when_persistence_is_disabled() {
        let pm_uid = "persistence_disabled_user";
        let Setup { service, db_addr, harness, _persistence_rx: _rx, .. } = setup(pm_uid).await;
        let (handler, _handler_rx) = connect_handler_with_metrics(db_addr, harness.metrics.clone());
        let config = SessionConfig { disable_persistence_on_close: true };
        handler.key_sync_handler(key_sync_request(pm_uid, Some(config))).await.unwrap();
        add_tagged(&handler, "unsynced").await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let dek_old = ctx.dek.clone();

        let status = rotate_dek(Some(&mut *ctx), &harness.metrics).await.unwrap_err();

        assert_eq!(status.code(), Code::FailedPrecondition, "{status:?}");
        assert_eq!(
            harness
                .collect()
                .counter("dek_rotation_count", &[("response_type", "unauthenticated")]),
            1
        );
        assert_eq!(
            rotation_latency_count(
                &harness,
                &[("status", "failure"), ("bytes_tier", "unknown"), ("blobs_tier", "unknown")]
            ),
            1
        );
        assert!(ctx.database.changed());
        assert_eq!(*stored_dek(&service, pm_uid, &ctx.kek).await, *dek_old);
        assert_eq!(service.lock_state.held_token(pm_uid).await, None);

        sync_persist_database(ctx, &harness.metrics).await.unwrap();
        rotate_dek(Some(&mut *ctx), &harness.metrics).await.expect("rotation after sync failed");
        assert_ne!(*ctx.dek, *dek_old);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn rotation_gives_up_once_it_has_held_the_lock_for_max_hold() {
        let pm_uid = "hold_limit_user";
        let Setup { service, db_addr, handler, harness, _persistence_rx: _rx } =
            setup(pm_uid).await;
        let memories = vec![(add_tagged(&handler, "kept").await, "kept")];
        sync_persist_database(handler.session_context().await.as_mut().unwrap(), &harness.metrics)
            .await
            .unwrap();
        let (_arrived, release) = service.hold_next_metadata_write().await;
        let timing = LockTiming {
            heartbeat_interval: Duration::from_millis(20),
            max_hold: Duration::from_millis(500),
            ..LockTiming::default()
        };

        {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            let dek_old = ctx.dek.clone();
            let blobs_before = sorted_blob_ids(ctx);

            let status =
                rotate_dek_with_timing(Some(ctx), &harness.metrics, timing).await.unwrap_err();

            assert_eq!(status.code(), Code::DeadlineExceeded, "{status:?}");
            assert_eq!(
                harness
                    .collect()
                    .counter("dek_rotation_count", &[("response_type", "retry_error")]),
                1
            );
            assert_eq!(
                rotation_latency_count(
                    &harness,
                    &[("status", "failure"), ("bytes_tier", "unknown"), ("blobs_tier", "unknown")]
                ),
                1
            );
            assert_eq!(*ctx.dek, *dek_old);
            assert_eq!(sorted_blob_ids(ctx), blobs_before);
            assert_eq!(*stored_dek(&service, pm_uid, &ctx.kek).await, *dek_old);
            wait_for_lock_release(&service, pm_uid).await;
        }
        drop(release);
        assert_fresh_session_reads(db_addr, pm_uid, &memories).await;
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn rotation_aborts_and_rolls_back_when_the_heartbeat_loses_the_lock() {
        let pm_uid = "lost_heartbeat_user";
        let Setup { service, db_addr, handler, harness, _persistence_rx: _rx } =
            setup(pm_uid).await;
        let memories = vec![(add_tagged(&handler, "kept").await, "kept")];
        sync_persist_database(handler.session_context().await.as_mut().unwrap(), &harness.metrics)
            .await
            .unwrap();
        let stored_blobs_before = sorted_stored_blob_ids(&service).await;
        let (arrived, release) = service.hold_next_metadata_write().await;
        let timing = LockTiming {
            lease: Duration::from_secs(60),
            heartbeat_interval: Duration::from_millis(10),
            ..LockTiming::default()
        };

        {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            let dek_old = ctx.dek.clone();
            let blobs_before = sorted_blob_ids(ctx);
            let lose_the_lock = async {
                arrived.await.unwrap();
                service
                    .lock_state
                    .advance(timing.lease + CLOCK_SKEW_MARGIN + Duration::from_secs(1));
                let deadline = Instant::now() + Duration::from_secs(10);
                while harness.collect().counter("dek_rotation_lock_extend_failures", &[]) == 0 {
                    assert!(Instant::now() < deadline, "heartbeat did not notice the lost lease");
                    tokio::time::sleep(Duration::from_millis(5)).await;
                }
                release.send(()).unwrap();
            };

            let (result, ()) = tokio::join!(
                rotate_dek_with_timing(Some(ctx), &harness.metrics, timing),
                lose_the_lock
            );

            assert_eq!(result.unwrap_err().code(), Code::Aborted);
            assert_eq!(
                harness
                    .collect()
                    .counter("dek_rotation_count", &[("response_type", "retry_error")]),
                1
            );
            assert_eq!(
                rotation_latency_count(
                    &harness,
                    &[("status", "failure"), ("bytes_tier", "unknown"), ("blobs_tier", "unknown")]
                ),
                1
            );
            assert_eq!(*ctx.dek, *dek_old);
            assert_eq!(sorted_blob_ids(ctx), blobs_before);
            assert_eq!(*stored_dek(&service, pm_uid, &ctx.kek).await, *dek_old);
            assert_eq!(sorted_stored_blob_ids(&service).await, stored_blobs_before);
        }
        assert_fresh_session_reads(db_addr, pm_uid, &memories).await;
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn rollback_failure_returns_data_loss_and_records_internal_error_metric() {
        let pm_uid = "rollback_failure_user";
        let Setup { service, handler, harness, _persistence_rx: _rx, .. } = setup(pm_uid).await;
        add_tagged(&handler, "kept").await;
        sync_persist_database(handler.session_context().await.as_mut().unwrap(), &harness.metrics)
            .await
            .unwrap();
        let (arrived, release) = service.hold_next_metadata_write().await;
        let timing = LockTiming::default();

        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let expire_lock_before_commit = async {
            arrived.await.unwrap();
            service.lock_state.advance(timing.lease + CLOCK_SKEW_MARGIN + Duration::from_secs(1));
            release.send(()).unwrap();
        };

        let (result, ()) = tokio::join!(
            FAIL_UNDO_REPOINT
                .scope((), rotate_dek_with_timing(Some(ctx), &harness.metrics, timing)),
            expire_lock_before_commit
        );

        assert_eq!(result.unwrap_err().code(), Code::DataLoss);
        assert_eq!(
            harness.collect().counter("dek_rotation_count", &[("response_type", "internal_error")]),
            1
        );
        assert_eq!(
            rotation_latency_count(
                &harness,
                &[("status", "failure"), ("bytes_tier", "unknown"), ("blobs_tier", "unknown")]
            ),
            1
        );
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn stale_session_still_reads_old_blobs_while_the_host_soft_deletes_them() {
        let pm_uid = "soft_delete_reader_user";
        let Setup { service, db_addr, handler, harness, _persistence_rx: _rx } =
            setup(pm_uid).await;
        service.soft_delete_blobs.store(true, Ordering::SeqCst);
        let memory = add_tagged(&handler, "persisted").await;
        sync_persist_database(handler.session_context().await.as_mut().unwrap(), &harness.metrics)
            .await
            .unwrap();
        let (reader, _reader_rx) = connect_handler(db_addr);
        reader.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();

        rotate_dek(handler.session_context().await.as_mut(), &harness.metrics)
            .await
            .expect("rotation failed");

        assert_eq!(tags_of(&reader, &memory).await, Some(vec!["persisted".to_string()]));
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn rotation_moves_every_memory_to_the_new_dek() {
        let pm_uid = "happy_path_user";
        let Setup { service, db_addr, handler, harness, _persistence_rx: _rx } =
            setup(pm_uid).await;
        let mut memories = Vec::new();
        for tag in ["one", "two", "three"] {
            memories.push((add_tagged(&handler, tag).await, tag));
        }
        sync_persist_database(handler.session_context().await.as_mut().unwrap(), &harness.metrics)
            .await
            .unwrap();
        memories.push((add_tagged(&handler, "pending").await, "pending"));

        {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            let dek_old = ctx.dek.clone();
            let old_blobs = sorted_blob_ids(ctx);

            let response =
                rotate_dek(Some(&mut *ctx), &harness.metrics).await.expect("rotation failed");

            assert_eq!(response.reencrypted_memories_count, 4);
            assert!(response.reencrypted_bytes > 0);
            let snapshot = harness.collect();
            assert_eq!(snapshot.counter("dek_rotation_count", &[("response_type", "ok")]), 1);
            assert_eq!(snapshot.counter("dek_rotation_blobs_reencrypted_total", &[]), 4);
            assert_eq!(
                snapshot.counter("dek_rotation_bytes_reencrypted_total", &[]),
                response.reencrypted_bytes as u64
            );
            let blobs_per_run = snapshot.histogram("dek_rotation_blobs_per_run", &[]);
            assert_eq!((blobs_per_run.count, blobs_per_run.sum), (1, 4));
            let bytes_per_run = snapshot.histogram("dek_rotation_bytes_per_run", &[]);
            assert_eq!(
                (bytes_per_run.count, bytes_per_run.sum),
                (1, response.reencrypted_bytes as u64)
            );
            assert_eq!(snapshot.histogram("dek_rotation_throughput_bytes_per_sec", &[]).count, 1);
            assert_eq!(
                rotation_latency_count(
                    &harness,
                    &[("status", "success"), ("bytes_tier", "<1MB"), ("blobs_tier", "<10")]
                ),
                1
            );
            assert_ne!(*ctx.dek, *dek_old);
            assert_eq!(*stored_dek(&service, pm_uid, &ctx.kek).await, *ctx.dek);
            assert_eq!(service.lock_state.held_token(pm_uid).await, None);
            assert!(!ctx.database.changed());
            let stored_version =
                service.metadata_database.lock().await.get(pm_uid).unwrap().version.clone();
            assert_eq!(ctx.database_version, stored_version);
            let blobs = service.database.lock().await;
            for (memory_id, blob_id) in old_blobs {
                assert!(!blobs.contains_key(&blob_id), "{memory_id}'s old blob was not deleted");
            }
        }

        for (id, tag) in &memories {
            assert_eq!(tags_of(&handler, id).await, Some(vec![tag.to_string()]));
        }
        assert_fresh_session_reads(db_addr, pm_uid, &memories).await;
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn lock_lost_before_commit_rolls_back_and_discards_the_copies() {
        let pm_uid = "lock_lost_user";
        let Setup { service, db_addr, handler, harness, _persistence_rx: _rx } =
            setup(pm_uid).await;
        let mut memories = vec![(add_tagged(&handler, "kept").await, "kept")];
        let metrics = harness.metrics.clone();
        let timing = LockTiming::default();

        {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            let dek_old = ctx.dek.clone();
            let (token, heartbeat) = acquire_row_lock(ctx, &metrics, timing).await.unwrap();
            catch_up_with_storage(ctx, &metrics, &token).await.unwrap();
            let blobs_before = sorted_blob_ids(ctx);
            let stored_before = service.metadata_database.lock().await.get(pm_uid).cloned();
            let (dek_new, data_blob) = generate_wrapped_dek_blob(
                &ctx.uid,
                &ctx.kek,
                ctx.database.key_derivation_info().clone(),
            )
            .unwrap();
            let reencryption = reencrypt_all_memory_blobs(ctx, &dek_new, &heartbeat).await.unwrap();

            service.lock_state.advance(timing.lease + CLOCK_SKEW_MARGIN + Duration::from_secs(1));
            service.lock_state.lock(pm_uid).await;

            let error =
                commit_or_roll_back(ctx, &token, &dek_new, data_blob, &reencryption, &heartbeat)
                    .await
                    .unwrap_err();

            assert_eq!(error.code(), Code::Aborted, "{error:?}");
            assert_eq!(sorted_blob_ids(ctx), blobs_before);
            assert_eq!(*ctx.dek, *dek_old);
            assert_eq!(service.metadata_database.lock().await.get(pm_uid).cloned(), stored_before);
            assert_eq!(*stored_dek(&service, pm_uid, &ctx.kek).await, *dek_old);
            let stored_blobs = service.database.lock().await;
            for (memory_id, _, copy) in &reencryption.repoints {
                assert!(!stored_blobs.contains_key(copy), "{memory_id}'s copy was kept");
            }
            drop(stored_blobs);
            service.lock_state.unlock(pm_uid).await;
        }

        memories.push((add_tagged(&handler, "after").await, "after"));
        sync_persist_database(handler.session_context().await.as_mut().unwrap(), &metrics)
            .await
            .unwrap();
        for (id, tag) in &memories {
            assert_eq!(tags_of(&handler, id).await, Some(vec![tag.to_string()]));
        }
        assert_fresh_session_reads(db_addr, pm_uid, &memories).await;
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn rotation_skips_memories_whose_blob_is_gone() {
        let pm_uid = "missing_blob_user";
        let Setup { service, db_addr, handler, harness, _persistence_rx: _rx } =
            setup(pm_uid).await;
        let kept = add_tagged(&handler, "kept").await;
        let lost = add_tagged(&handler, "lost").await;
        let expired = {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            let expired = ctx
                .database
                .add_memory(memory_expiring_at(
                    "expired",
                    SystemTime::now() - Duration::from_secs(60),
                ))
                .await
                .unwrap();
            sync_persist_database(ctx, &harness.metrics).await.unwrap();
            expired
        };

        {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            let blob_ids: HashMap<_, _> =
                ctx.database.get_all_memory_and_blob_ids().unwrap().into_iter().collect();
            let mut blobs = service.database.lock().await;
            blobs.remove(&blob_ids[&lost]).unwrap();
            blobs.remove(&blob_ids[&expired]).unwrap();
        }

        let response = {
            let mut guard = handler.session_context().await;
            rotate_dek(guard.as_mut(), &harness.metrics).await.unwrap()
        };

        assert_eq!(response.reencrypted_memories_count, 1);
        assert_eq!(harness.collect().counter("dek_rotation_blobs_reencrypted_total", &[]), 1);
        assert_fresh_session_reads(db_addr, pm_uid, &[(kept, "kept")]).await;
        let (reader, _persistence_rx) = connect_handler(db_addr);
        reader.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        assert_eq!(tags_of(&reader, &expired).await, None);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn cancelled_rotation_releases_the_row_lock() {
        let pm_uid = "cancelled_rotation_user";
        let Setup { service, handler, harness, _persistence_rx: _rx, .. } = setup(pm_uid).await;
        add_tagged(&handler, "pending").await;
        let (arrived, release) = service.hold_next_metadata_write().await;

        {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            tokio::select! {
                _ = rotate_dek(Some(&mut *ctx), &harness.metrics) => {
                    panic!("rotation finished while held")
                }
                _ = arrived => {}
            }
        }
        drop(release);

        wait_for_lock_release(&service, pm_uid).await;
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn session_can_rotate_twice() {
        let pm_uid = "rotate_twice_user";
        let Setup { service, db_addr, handler, harness, _persistence_rx: _rx } =
            setup(pm_uid).await;
        let mut memories = vec![(add_tagged(&handler, "first").await, "first")];

        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        rotate_dek(Some(&mut *ctx), &harness.metrics).await.expect("first rotation failed");
        let dek_after_first = ctx.dek.clone();
        rotate_dek(Some(&mut *ctx), &harness.metrics).await.expect("second rotation failed");
        assert_ne!(*ctx.dek, *dek_after_first);
        assert_eq!(*stored_dek(&service, pm_uid, &ctx.kek).await, *ctx.dek);
        drop(guard);

        memories.push((add_tagged(&handler, "after").await, "after"));
        sync_persist_database(handler.session_context().await.as_mut().unwrap(), &harness.metrics)
            .await
            .unwrap();
        assert_eq!(harness.collect().counter("dek_rotation_count", &[("response_type", "ok")]), 2);
        assert_fresh_session_reads(db_addr, pm_uid, &memories).await;
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn stale_session_rotates_after_another_rotation() {
        let pm_uid = "stale_rotator_user";
        let Setup { service, db_addr, handler, harness, _persistence_rx: _rx } =
            setup(pm_uid).await;
        let mut memories = vec![(add_tagged(&handler, "persisted").await, "persisted")];
        sync_persist_database(handler.session_context().await.as_mut().unwrap(), &harness.metrics)
            .await
            .unwrap();

        let (stale, _stale_rx) = connect_handler_with_metrics(db_addr, harness.metrics.clone());
        stale.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        memories.push((add_tagged(&stale, "stale-pending").await, "stale-pending"));
        let stale_dek = stale.session_context().await.as_ref().unwrap().dek.clone();

        let first_dek = {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            rotate_dek(Some(&mut *ctx), &harness.metrics).await.expect("first rotation failed");
            ctx.dek.clone()
        };

        let mut guard = stale.session_context().await;
        let ctx = guard.as_mut().unwrap();
        rotate_dek(Some(&mut *ctx), &harness.metrics)
            .await
            .expect("stale session's rotation failed");
        assert_ne!(*ctx.dek, *stale_dek);
        assert_ne!(*ctx.dek, *first_dek);
        assert_eq!(*stored_dek(&service, pm_uid, &ctx.kek).await, *ctx.dek);
        drop(guard);

        assert_fresh_session_reads(db_addr, pm_uid, &memories).await;
    }
}
