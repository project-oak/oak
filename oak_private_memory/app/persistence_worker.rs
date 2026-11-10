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
    sync::{Arc, Mutex, PoisonError},
    time::Duration,
};

use anyhow::Context;
use external_db_client::{DataBlobHandler, MetadataBlobRead, MetadataPersistResult};
use log::{error, info, warn};
use metrics::Metrics;
use oak_private_memory_database::encryption::{decrypt_database, encrypt_database};
use prost::Message;
use rand::Rng;
use sealed_memory_rust_proto::{
    oak::private_memory::EncryptedMetadataBlob, prelude::v1::SyncDatabaseResponse,
};
use tokio::{
    sync::{OwnedSemaphorePermit, Semaphore, mpsc},
    task::JoinSet,
    time::Instant,
};

/// Maximum number of attempts to persist the database when its write hits a
/// version conflict. Retries of host `RESOURCE_EXHAUSTED` rejections and of
/// writes refused by another writer's row lock don't count towards this: each
/// database call's `RESOURCE_EXHAUSTED` retries are bounded by a
/// [`ResourceExhaustedRetryPolicy`], and row lock waits by a
/// [`LockWaitPolicy`], instead.
static MAX_RETRY_ATTEMPTS: u64 = 25;

/// Maximum number of user sessions persisted concurrently by the background
/// persistence worker.
pub(crate) const MAX_CONCURRENT_PERSISTS: usize = 8;

/// Retry policy of the persistence worker, which persists sessions in the
/// background after they close.
///
/// Nobody waits for it, and giving up drops the session's changes, so it is
/// patient: each database call rides out up to 5 minutes of host memory
/// pressure, which is long enough for the host to shed load (or for its memory
/// to be freed by requests completing) in all but a sustained overload. Sleeps
/// are capped at 10 seconds so that the worker notices quickly when the
/// pressure ends.
///
/// While all `MAX_CONCURRENT_PERSISTS` slots are backing off, sessions that
/// close in the meantime queue up behind them in TEE memory. That is
/// preferable to dropping their changes, and TEE memory pressure is handled by
/// admission control, which rejects new sessions when TEE memory runs low.
const PERSISTENCE_WORKER_RETRY_POLICY: ResourceExhaustedRetryPolicy =
    ResourceExhaustedRetryPolicy {
        initial_backoff: Duration::from_millis(200),
        max_backoff: Duration::from_secs(10),
        total_budget: Duration::from_secs(5 * 60),
    };

/// Retry policy of the SyncDatabase RPC.
///
/// A client is waiting for the RPC, and holds the session meanwhile, so each
/// database call's budget is short: 30 seconds rides out a transient spike of
/// host memory pressure, and beyond that the RPC fails as before. An RPC makes
/// at least two database calls (the pull and the push), plus a write and a
/// pull per version conflict. The session's changes are not lost when it
/// fails: they stay in the session.
const SYNC_DATABASE_RETRY_POLICY: ResourceExhaustedRetryPolicy = ResourceExhaustedRetryPolicy {
    initial_backoff: Duration::from_millis(200),
    max_backoff: Duration::from_secs(5),
    total_budget: Duration::from_secs(30),
};

/// Retry policy of the rebase pull and the persist write that DEK rotation
/// makes under its row lock.
///
/// Like SyncDatabase, the RotateDek RPC has a client waiting, so each database
/// call rides out up to 30 seconds of host memory pressure. Beyond that, the
/// rejection is returned, and the RotateDek caller sees `RESOURCE_EXHAUSTED`
/// and may retry. The rotation's heartbeat keeps the row lock alive meanwhile.
const LOCKED_PERSIST_RETRY_POLICY: ResourceExhaustedRetryPolicy = SYNC_DATABASE_RETRY_POLICY;

/// A [`ResourceExhaustedRetryPolicy`] with millisecond backoffs, for tests.
#[cfg(test)]
pub(crate) const TEST_RETRY_POLICY: ResourceExhaustedRetryPolicy = ResourceExhaustedRetryPolicy {
    initial_backoff: Duration::from_millis(2),
    max_backoff: Duration::from_millis(10),
    total_budget: Duration::from_secs(10),
};

/// A bounded, jittered exponential backoff policy for retrying database calls
/// that the host rejects with `RESOURCE_EXHAUSTED`.
///
/// The untrusted host rejects database calls with `RESOURCE_EXHAUSTED` when
/// it is close to running out of memory: reads first, and writes once memory
/// is even tighter. It rejects them before doing any work, so retrying them is
/// safe, and the condition is usually transient. (Any `RESOURCE_EXHAUSTED`
/// from the host is retried, but the budget bounds retrying one that isn't.)
///
/// Each database call (e.g. one metadata blob read or write) gets its own
/// budget.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ResourceExhaustedRetryPolicy {
    /// The upper bound of the first sleep. Each further sleep doubles it, up
    /// to `max_backoff`. Each sleep is jittered between half its bound and its
    /// bound, so that sessions rejected at the same time don't retry in
    /// lockstep.
    initial_backoff: Duration,
    /// The upper bound of any sleep.
    max_backoff: Duration,
    /// The total time to keep retrying one database call for, from its first
    /// rejection. A retry whose sleep would end after this is not attempted:
    /// the rejection is returned instead.
    total_budget: Duration,
}

/// The state of retrying one database call that the host rejects with
/// `RESOURCE_EXHAUSTED`.
pub(crate) struct ResourceExhaustedBackoff {
    policy: ResourceExhaustedRetryPolicy,
    /// When the first rejection was seen, if any.
    first_rejection: Option<Instant>,
    /// The upper bound of the next sleep.
    next_backoff: Duration,
    /// The number of retries so far.
    retries: u64,
}

impl ResourceExhaustedBackoff {
    pub(crate) fn new(policy: ResourceExhaustedRetryPolicy) -> Self {
        Self { policy, first_rejection: None, next_backoff: policy.initial_backoff, retries: 0 }
    }

    /// Handles the `error` that a database call for `operation` failed with.
    ///
    /// If the host rejected the call with `RESOURCE_EXHAUSTED`, and the budget
    /// allows another attempt, sleeps and returns `Ok`: the caller should
    /// retry the call. Otherwise returns the error.
    pub(crate) async fn wait_to_retry(
        &mut self,
        error: anyhow::Error,
        operation: &str,
        metrics: &Metrics,
    ) -> anyhow::Result<()> {
        if !is_resource_exhausted(&error) {
            return Err(error);
        }
        let first_rejection = *self.first_rejection.get_or_insert_with(Instant::now);
        // Equal jitter: sleep for between half the backoff and the backoff.
        let half_backoff = self.next_backoff / 2;
        let sleep = half_backoff + half_backoff.mul_f64(rand::random::<f64>());
        let retrying_for = first_rejection.elapsed();
        if retrying_for + sleep > self.policy.total_budget {
            warn!(
                "host rejected {operation} with RESOURCE_EXHAUSTED, giving up after {} retries \
                 over {retrying_for:?}",
                self.retries
            );
            return Err(error.context(format!(
                "host rejected {operation} with RESOURCE_EXHAUSTED {} times in {retrying_for:?}",
                self.retries + 1
            )));
        }
        self.retries += 1;
        metrics.inc_db_resource_exhausted_retries();
        warn!(
            "host rejected {operation} with RESOURCE_EXHAUSTED, retry {} in {sleep:?}",
            self.retries
        );
        tokio::time::sleep(sleep).await;
        self.next_backoff = (self.next_backoff * 2).min(self.policy.max_backoff);
        Ok(())
    }
}

/// Returns whether `error` is a gRPC `RESOURCE_EXHAUSTED` status, which is how
/// the host rejects database calls under memory pressure. The database client
/// returns the host's status as the error itself.
fn is_resource_exhausted(error: &anyhow::Error) -> bool {
    error
        .downcast_ref::<tonic::Status>()
        .is_some_and(|status| status.code() == tonic::Code::ResourceExhausted)
}

/// How long a background persist waits out a row locked by another writer
/// before it gives up and drops the session's writes.
///
/// A DEK rotation holds the row for at most 10 minutes and leaves at most one
/// 90s lease behind when it stops renewing; 15 minutes covers that with margin.
pub(crate) const BACKGROUND_LOCK_WAIT: Duration = Duration::from_secs(15 * 60);

/// Wait budget and retry schedule when persisting a row locked by another
/// writer.
///
/// Storage only refuses a write to a locked row after receiving all of it, so
/// every retry re-exports, re-encrypts and re-uploads the whole database. The
/// delay between retries therefore doubles from `first_delay` up to
/// `max_delay`: a short lock is picked up within seconds, while a lock held for
/// the whole budget costs a few dozen uploads instead of hundreds. Each delay
/// is jittered down by up to half, so sessions waiting on the same row don't
/// retry in lockstep.
#[derive(Clone, Debug)]
struct LockWaitPolicy {
    /// Wall-clock budget, counted from the first refused write. It includes any
    /// time the retries in between spend riding out host `RESOURCE_EXHAUSTED`
    /// rejections.
    max_wait: Duration,
    /// Ceiling of the delay after the first refused write; the actual delay is
    /// between half of it and all of it.
    first_delay: Duration,
    /// Cap on the doubling ceiling.
    max_delay: Duration,
}

impl LockWaitPolicy {
    /// Policy for `run_persistence_service`: waits up to
    /// [`BACKGROUND_LOCK_WAIT`]. A row locked for the whole budget is retried
    /// about 25 times.
    fn for_background_persist() -> Self {
        Self {
            max_wait: BACKGROUND_LOCK_WAIT,
            first_delay: Duration::from_secs(2),
            max_delay: Duration::from_secs(60),
        }
    }

    /// Policy for `SyncDatabase`, which blocks the caller's RPC and fails with
    /// [`RowLocked`] after 10s.
    fn for_sync() -> Self {
        Self {
            max_wait: Duration::from_secs(10),
            first_delay: Duration::from_millis(500),
            max_delay: Duration::from_secs(2),
        }
    }

    /// Returns the delay before retrying after the `conflicts`-th refused write
    /// (counting from 1), before capping it at the remaining budget.
    fn retry_delay(&self, conflicts: u32) -> Duration {
        let doublings = conflicts.saturating_sub(1).min(31);
        let ceiling = self.first_delay.saturating_mul(1 << doublings).min(self.max_delay);
        rand::rng().random_range(ceiling / 2..=ceiling)
    }
}

/// The background worker's `MAX_CONCURRENT_PERSISTS` slots and the state its
/// persist tasks share.
#[derive(Clone)]
struct PersistSlots {
    semaphore: Arc<Semaphore>,
    /// Number of sessions taken off the worker's queue that are waiting for a
    /// slot or waiting out a row lock. They count as queued in
    /// `db_persist_queue_size`; the lock serializes updating the count with
    /// recording the gauge.
    waiting: Arc<Mutex<u64>>,
}

impl PersistSlots {
    fn new() -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(MAX_CONCURRENT_PERSISTS)),
            waiting: Arc::new(Mutex::new(0)),
        }
    }

    /// Claims a slot for a session, reusing `permit` if the coordinator already
    /// claimed one for it. The session counts as queued until it has a slot.
    async fn claim(&self, permit: Option<OwnedSemaphorePermit>, metrics: &Metrics) -> PersistSlot {
        let mut slot = PersistSlot { slots: self.clone(), permit };
        if slot.permit.is_none() {
            let _counted = Waiting::start(&self.waiting, metrics);
            slot.reacquire().await;
        }
        slot
    }

    /// Records `queued` sessions still in the worker's queue, plus the
    /// [`Self::waiting`] ones, as `db_persist_queue_size`.
    fn record_queue_size(&self, queued: usize, metrics: &Metrics) {
        let waiting = self.waiting.lock().unwrap_or_else(PoisonError::into_inner);
        metrics.record_db_persist_queue_size(queued as u64 + *waiting);
    }
}

/// A background persist's claim on one of the worker's
/// `MAX_CONCURRENT_PERSISTS` slots. The persist gives the slot up while it
/// waits out a row lock, so that other queued sessions can persist.
struct PersistSlot {
    slots: PersistSlots,
    permit: Option<OwnedSemaphorePermit>,
}

impl PersistSlot {
    async fn reacquire(&mut self) {
        if self.permit.is_none() {
            let permit = self
                .slots
                .semaphore
                .clone()
                .acquire_owned()
                .await
                .expect("persist slots are never closed");
            self.permit = Some(permit);
        }
    }

    /// Waits `delay` without holding a slot, then takes a slot again, counted
    /// as queued in `db_persist_queue_size` throughout.
    async fn wait_without_slot(&mut self, delay: Duration, metrics: &Metrics) {
        self.permit = None;
        let waiting = self.slots.waiting.clone();
        let _counted = Waiting::start(&waiting, metrics);
        tokio::time::sleep(delay).await;
        self.reacquire().await;
    }
}

/// Counts a session in [`PersistSlots::waiting`] and `db_persist_queue_size`
/// until dropped.
struct Waiting<'a> {
    waiting: &'a Mutex<u64>,
    metrics: &'a Metrics,
}

impl<'a> Waiting<'a> {
    fn start(waiting: &'a Mutex<u64>, metrics: &'a Metrics) -> Self {
        let mut count = waiting.lock().unwrap_or_else(PoisonError::into_inner);
        *count += 1;
        metrics.inc_db_persist_queue_size();
        drop(count);
        Self { waiting, metrics }
    }
}

impl Drop for Waiting<'_> {
    fn drop(&mut self) {
        let mut count = self.waiting.lock().unwrap_or_else(PoisonError::into_inner);
        *count -= 1;
        self.metrics.dec_db_persist_queue_size();
    }
}

#[derive(Debug, Default)]
struct LockWaits {
    conflicts: u32,
    first_conflict: Option<Instant>,
    waited: Duration,
}

/// Returned when a persist gives up because another writer held the user's row
/// past [`LockWaitPolicy::max_wait`].
#[derive(Debug)]
pub(crate) struct RowLocked {
    waited: Duration,
    rejected_attempts: u32,
}

impl std::fmt::Display for RowLocked {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "the user's row stayed locked by another writer for {:?} ({} rejected attempts)",
            self.waited, self.rejected_attempts
        )
    }
}

impl std::error::Error for RowLocked {}

#[cfg(test)]
impl RowLocked {
    pub(crate) fn for_test() -> Self {
        Self { waited: Duration::ZERO, rejected_attempts: 1 }
    }
}

/// Returned when a write under the row lock finds that the lock lapsed (storage
/// refused the lock token or the row version changed).
#[derive(Debug)]
pub(crate) struct RowLockLost;

impl std::fmt::Display for RowLockLost {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "the row lock was lost while writing under it")
    }
}

impl std::error::Error for RowLockLost {}

/// Minimum number of optimizable (deleted/expired) documents before calling
/// Icing.Optimize. GetOptimizeInfo (~0.16ms) is called on every persist to
/// check, and Optimize (~1s) is only called when this threshold is exceeded.
pub(crate) const OPTIMIZE_DOC_THRESHOLD: i64 = 100;

use crate::{
    context::UserSessionContext,
    dek::{DekNotRotated, switch_to_stored_dek},
};

/// Attempts to persist the database once, if it changed, presenting
/// `lock_token` for the row (empty if the caller holds no lock).
///
/// If the write hits a version mismatch, returns
/// `Ok(MetadataPersistResult::RetryNeeded)` so the caller can re-fetch the
/// latest metadata blob, rebase the icing database, and try again. If another
/// writer holds the row lock, returns
/// `Ok(MetadataPersistResult::LockConflict)`.
///
/// The database is exported and encrypted once. If the host rejects the write
/// with `RESOURCE_EXHAUSTED`, the same encrypted database is sent again, as far
/// as `policy` allows.
async fn try_persist_database(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
    policy: ResourceExhaustedRetryPolicy,
    lock_token: &str,
) -> anyhow::Result<MetadataPersistResult> {
    if !user_context.database.changed() {
        info!("Database is not changed, skip saving");
        return Ok(MetadataPersistResult::Succeeded { committed_version: None });
    }
    let exported_db = user_context.database.export()?;
    let encrypted_info = exported_db.encrypted_info.context("encrypted info is empty")?;
    let database = encrypt_database(&encrypted_info, &user_context.dek)?;

    let db_size = database.data.len();
    let max_database_size = user_context.database.max_size();
    if db_size > max_database_size {
        warn!(
            "Database exceeds maximum size limit: {} (limit: {}), saving anyway to prevent data loss",
            db_size, max_database_size
        );
    }
    info!("Saving db size: {}", db_size);
    let encoded_size = database.encoded_len();

    let metadata_blob = EncryptedMetadataBlob {
        encrypted_data_blob: Some(database),
        version: user_context.database_version.clone(),
    };
    let coarsened_expiration_timestamp = user_context.database.calculate_coarsened_blanket_ttl();
    let mut backoff = ResourceExhaustedBackoff::new(policy);
    let (result, elapsed) = loop {
        let now = Instant::now();
        match user_context
            .database_service_client
            .add_metadata_blob_stream_with_lock(
                &user_context.uid,
                &metadata_blob,
                coarsened_expiration_timestamp,
                lock_token,
                /* unencrypted_data_blob= */ None,
            )
            .await
        {
            Ok(result) => break (result, now.elapsed()),
            Err(e) => backoff.wait_to_retry(e, "metadata blob write", metrics).await?,
        }
    };
    drop(metadata_blob);

    if matches!(result, MetadataPersistResult::Succeeded { .. }) {
        metrics.record_db_persist_latency(elapsed.as_millis() as u64);
        metrics.record_db_size(db_size as u64);
        metrics.record_db_save_speed(metrics::transfer_speed_kb_per_ms(encoded_size, elapsed));
    }

    Ok(result)
}

/// How many times [`pull_and_rebase`] fetches the metadata blob again after
/// moving the session onto a rotated DEK that the fetched blob still doesn't
/// decrypt under. That happens when another rotation commits between fetching
/// the blob and reading the stored DEK; each re-fetch follows one more
/// rotation.
const MAX_ROTATED_BLOB_REFETCHES: usize = 3;

/// Fetch the latest remote blob and rebase the local database onto it.
///
/// If `require_blob` is true, a missing blob is an error (used on CAS retry,
/// after the write was rejected because the blob changed). If false, a missing
/// blob is silently skipped (used for SyncDatabase, where the user may not have
/// any persisted data yet), and the host skips sending the blob if it still has
/// the session's `database_version`.
///
/// If the blob doesn't decrypt under the session DEK because another session
/// rotated the DEK, moves the session onto the stored DEK (see
/// [`switch_to_stored_dek`]) first, fetching the blob again if it predates the
/// stored DEK.
///
/// Retries the fetch, and the database calls of a DEK switch, while the host
/// rejects them with `RESOURCE_EXHAUSTED`, as far as `policy` allows.
async fn pull_and_rebase(
    user_context: &mut UserSessionContext,
    require_blob: bool,
    metrics: &Metrics,
    policy: ResourceExhaustedRetryPolicy,
) -> anyhow::Result<()> {
    let coarsened_expiration_timestamp = user_context.database.calculate_coarsened_blanket_ttl();
    // Send the session's version, so that an unchanged blob isn't downloaded
    // again. On CAS retry the blob is known to have changed, so don't.
    let mut known_version = (!require_blob && !user_context.database_version.is_empty())
        .then(|| user_context.database_version.clone());
    let mut refetches = 0;
    let (version, decrypted) = loop {
        let mut backoff = ResourceExhaustedBackoff::new(policy);
        let (refreshed_blob, fetch_elapsed) = loop {
            let fetch_start = Instant::now();
            match user_context
                .database_service_client
                .get_metadata_blob_stream(
                    &user_context.uid,
                    coarsened_expiration_timestamp,
                    known_version.as_deref(),
                )
                .await
            {
                Ok(blob) => break (blob, fetch_start.elapsed()),
                Err(e) => backoff.wait_to_retry(e, "metadata blob read", metrics).await?,
            }
        };

        let refreshed_blob = match refreshed_blob {
            MetadataBlobRead::Blob(blob) => blob,
            MetadataBlobRead::NotModified => {
                metrics.inc_db_pull_skipped_count();
                return Ok(());
            }
            MetadataBlobRead::NotFound if require_blob => anyhow::bail!("no blob found"),
            MetadataBlobRead::NotFound => return Ok(()),
        };
        if let Some(encrypted_data_blob) = &refreshed_blob.encrypted_data_blob {
            metrics.record_db_load_speed(metrics::transfer_speed_kb_per_ms(
                encrypted_data_blob.encoded_len(),
                fetch_elapsed,
            ));
        }

        if refreshed_blob.version == user_context.database_version {
            return Ok(());
        }

        let encrypted_data_blob =
            refreshed_blob.encrypted_data_blob.context("missing encrypted data blob")?;
        // If decryption fails, check whether another session rotated the DEK
        // before counting a decryption failure.
        let decrypt_error = match decrypt_database(&encrypted_data_blob, &user_context.dek) {
            Ok(decrypted) => break (refreshed_blob.version, decrypted),
            Err(decrypt_error) => decrypt_error,
        };
        info!("metadata blob does not decrypt under the session DEK, checking for a rotation");
        if let Err(e) = switch_to_stored_dek(user_context, metrics, policy).await {
            if e.is::<DekNotRotated>() {
                error!("decrypting metadata blob under the stored DEK: {decrypt_error:?}");
                metrics.inc_db_decryption_failures();
            }
            return Err(e.context(format!("metadata blob undecryptable: {decrypt_error:?}")));
        }
        match decrypt_database(&encrypted_data_blob, &user_context.dek) {
            Ok(decrypted) => break (refreshed_blob.version, decrypted),
            // Another rotation committed after the blob was fetched, so the
            // blob predates the stored DEK the session just moved onto. Fetch
            // the blob again: it is encrypted under the stored DEK, unless it
            // is corrupt, which the next pass detects (the stored DEK is then
            // the session's DEK, so the switch fails with `DekNotRotated`).
            Err(e) if refetches < MAX_ROTATED_BLOB_REFETCHES => {
                info!("metadata blob predates the stored DEK, fetching it again: {e:?}");
                refetches += 1;
                known_version = None;
            }
            Err(e) => {
                return Err(e.context(format!(
                    "metadata blob still predates the stored DEK after {refetches} re-fetches"
                )));
            }
        }
    };
    let new_icing_db = decrypted.icing_db.context("missing icing_db in refreshed blob")?;
    let failed_operations =
        user_context.database.rebase(new_icing_db.encode_to_vec().as_slice())?;
    if failed_operations > 0 {
        // TODO: b/571198870 - not covered by a metric test: replaying a
        // pending operation onto the refreshed database only fails when icing
        // itself rejects the put/delete/reset (deletes of memories that are
        // already gone are skipped), and there is no icing fault-injection
        // hook to trigger that.
        metrics.inc_db_rebase_operation_failures(failed_operations as u64);
    }
    user_context.database_version = version;
    Ok(())
}

fn maybe_optimize(
    database: &mut oak_private_memory_database::Database,
    metrics: &Metrics,
) -> anyhow::Result<()> {
    let info = database.get_optimize_info().context("getting optimize info")?;
    if info.optimizable_docs() > OPTIMIZE_DOC_THRESHOLD {
        info!("optimizing database ({} optimizable docs)", info.optimizable_docs());
        let now = Instant::now();
        database.optimize().context("optimizing database")?;
        let elapsed = now.elapsed();
        metrics.record_db_optimize_latency(elapsed.as_millis() as u64);
    }
    Ok(())
}

/// Synchronously persist the database.
///
/// This is the public API for the SyncDatabase RPC handler. It pulls the latest
/// remote state (which may include writes from other sessions), rebases the
/// local database, optimizes if needed, then pushes any local changes.
///
/// Database calls that the host rejects with `RESOURCE_EXHAUSTED` are retried
/// according to [`SYNC_DATABASE_RETRY_POLICY`]. Fails with [`RowLocked`] if the
/// user's row stays locked past [`LockWaitPolicy::for_sync`].
pub async fn sync_persist_database(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
) -> anyhow::Result<SyncDatabaseResponse> {
    sync_persist_database_with_policy(
        user_context,
        metrics,
        SYNC_DATABASE_RETRY_POLICY,
        LockWaitPolicy::for_sync(),
    )
    .await
}

async fn sync_persist_database_with_policy(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
    policy: ResourceExhaustedRetryPolicy,
    lock_wait: LockWaitPolicy,
) -> anyhow::Result<SyncDatabaseResponse> {
    // Pull: fetch the latest remote blob and rebase so that remote changes
    // become visible in this session's local database.
    pull_and_rebase(user_context, /* require_blob= */ false, metrics, policy).await?;

    // Optimize is expensive (~1s for a 30MB database) and always rebuilds
    // the entire index. Use GetOptimizeInfo (~0.16ms) to check whether
    // there are enough deleted/expired documents to warrant optimization.
    maybe_optimize(&mut user_context.database, metrics)?;

    // Push: persist any local changes (now rebased on top of the latest remote
    // state).
    persist_database_with_policy(user_context, metrics, policy, lock_wait, None).await?;

    Ok(SyncDatabaseResponse {})
}

async fn persist_one_session(
    mut user_context: UserSessionContext,
    metrics: Arc<Metrics>,
    mut slot: PersistSlot,
) {
    // Optimize is expensive (~1s for a 30MB database) and always rebuilds
    // the entire index. Use GetOptimizeInfo (~0.16ms) to check whether
    // there are enough deleted/expired documents to warrant optimization.
    if let Err(e) = maybe_optimize(&mut user_context.database, &metrics) {
        error!("optimizing database: {e:?}");
    }

    if let Err(e) = persist_database_with_policy(
        &mut user_context,
        &metrics,
        PERSISTENCE_WORKER_RETRY_POLICY,
        LockWaitPolicy::for_background_persist(),
        Some(&mut slot),
    )
    .await
    {
        metrics.inc_db_persist_failures();
        error!("Failed to persist database: {:?}", e);
    }
}

async fn finish_persist(user_context: &mut UserSessionContext, metrics: &Metrics) {
    // Flush deferred blob soft-deletes now that the index is durably
    // persisted. Orphaned blobs are tracked in metrics and can be cleaned by
    // GC.
    let pending_count = user_context.database.meta_db().pending_blob_deletes().len();
    if let Err(e) = user_context.database.flush_pending_blob_deletes().await {
        metrics.inc_orphaned_blob_deletes(pending_count as u64);
        error!("{e}");
    }
    user_context.database.mark_persisted();
}

/// Fetches the latest stored metadata blob, if any, and rebases the session
/// onto it.
///
/// A read that the host rejects with `RESOURCE_EXHAUSTED` is retried according
/// to [`LOCKED_PERSIST_RETRY_POLICY`].
pub(crate) async fn rebase_onto_storage(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
) -> anyhow::Result<()> {
    pull_and_rebase(
        user_context,
        /* require_blob= */ false,
        metrics,
        LOCKED_PERSIST_RETRY_POLICY,
    )
    .await
}

/// Persists pending changes under `lock_token` and adopts the version the host
/// reports for the write. Fails with [`RowLockLost`] if storage refuses the
/// lock token or reports a version conflict (while the lock is held, only
/// another writer after a lapsed lock can move the version).
///
/// A write that the host rejects with `RESOURCE_EXHAUSTED` is retried according
/// to [`LOCKED_PERSIST_RETRY_POLICY`].
pub(crate) async fn persist_under_lock(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
    lock_token: &str,
) -> anyhow::Result<()> {
    if !user_context.database.changed() {
        return Ok(());
    }
    match try_persist_database(user_context, metrics, LOCKED_PERSIST_RETRY_POLICY, lock_token)
        .await?
    {
        MetadataPersistResult::Succeeded { committed_version } => {
            if let Some(committed_version) = committed_version {
                user_context.database_version = committed_version;
            }
            finish_persist(user_context, metrics).await;
            Ok(())
        }
        MetadataPersistResult::LockConflict | MetadataPersistResult::RetryNeeded => {
            Err(RowLockLost.into())
        }
    }
}

/// Persists the session, retrying version conflicts up to
/// `MAX_RETRY_ATTEMPTS` times.
///
/// Independently, database calls that the host rejects with
/// `RESOURCE_EXHAUSTED` are retried as far as `policy` allows, and row locks
/// are waited out per `lock_wait`; neither counts as an attempt. If `slot` is
/// given, it is released while waiting out a row lock.
async fn persist_database_with_policy(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
    policy: ResourceExhaustedRetryPolicy,
    lock_wait: LockWaitPolicy,
    slot: Option<&mut PersistSlot>,
) -> anyhow::Result<()> {
    let mut lock_waits = LockWaits::default();
    let result =
        persist_with_retries(user_context, metrics, policy, lock_wait, &mut lock_waits, slot).await;
    if lock_waits.conflicts > 0 {
        metrics.record_db_persist_lock_wait_latency(lock_waits.waited.as_millis() as u64);
    }
    result
}

async fn persist_with_retries(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
    policy: ResourceExhaustedRetryPolicy,
    lock_wait: LockWaitPolicy,
    lock_waits: &mut LockWaits,
    mut slot: Option<&mut PersistSlot>,
) -> anyhow::Result<()> {
    // `try_persist_database` skips writing a database without changes, so
    // that isn't a persist for the metrics below.
    let has_changes = user_context.database.changed();
    let mut attempt: u64 = 1;
    let now = Instant::now();
    while attempt < MAX_RETRY_ATTEMPTS {
        match try_persist_database(user_context, metrics, policy, /* lock_token= */ "").await? {
            MetadataPersistResult::Succeeded { committed_version } => {
                // Track our own write, so that the next sync doesn't mistake
                // it for a remote change. Without a version from the host,
                // keep the old one: the next sync then pulls our write back.
                if let Some(committed_version) = committed_version {
                    user_context.database_version = committed_version;
                }
                if has_changes {
                    // This includes any RESOURCE_EXHAUSTED backoff and row
                    // lock waits.
                    let elapsed = now.elapsed();
                    metrics.record_db_persist_latency_with_retries(elapsed.as_millis() as u64);
                    metrics.record_db_persist_attempts(attempt);
                }
                finish_persist(user_context, metrics).await;
                return Ok(());
            }
            MetadataPersistResult::RetryNeeded => {
                attempt += 1;
                info!("Retrying db save (attempt {attempt})");
                pull_and_rebase(user_context, /* require_blob= */ true, metrics, policy).await?;
            }
            MetadataPersistResult::LockConflict => {
                metrics.inc_db_persist_lock_conflicts();
                lock_waits.conflicts += 1;
                let first_conflict = *lock_waits.first_conflict.get_or_insert_with(Instant::now);

                let waited = first_conflict.elapsed();
                lock_waits.waited = waited;
                if waited >= lock_wait.max_wait {
                    return Err(
                        RowLocked { waited, rejected_attempts: lock_waits.conflicts }.into()
                    );
                }

                let delay =
                    lock_wait.retry_delay(lock_waits.conflicts).min(lock_wait.max_wait - waited);
                warn!(
                    "database row locked by another writer (conflict {conflicts}); waited \
                     {waited:?} of {max_wait:?} so far, retrying in {delay:?} without using the \
                     rebase budget",
                    conflicts = lock_waits.conflicts,
                    max_wait = lock_wait.max_wait,
                );
                match slot.as_deref_mut() {
                    Some(slot) => slot.wait_without_slot(delay, metrics).await,
                    None => tokio::time::sleep(delay).await,
                }
                lock_waits.waited = first_conflict.elapsed();
                // Skip pull_and_rebase: the write was refused before changing
                // remote state.
            }
        }
    }
    anyhow::bail!("Failed to persist after {} attempts", MAX_RETRY_ATTEMPTS);
}

/// Persists each session received on `rx` in its own task, with at most
/// `MAX_CONCURRENT_PERSISTS` persisting at once.
///
/// A session is only taken off `rx` when a worker slot is free, so sessions
/// waiting for a slot stay in `rx`. A session waiting out another writer's row
/// lock gives up its slot until it retries, so locked rows can't stall other
/// users' sessions. `db_persist_queue_size` counts the sessions in `rx` plus
/// the ones taken off it that are waiting for a slot or out a row lock.
///
/// Once `rx` is closed and empty (all senders are gone, e.g. because the gRPC
/// server exited), the service finishes the persists in progress and returns.
/// Each persist may wait up to [`BACKGROUND_LOCK_WAIT`] for a row lock or up to
/// the `PERSISTENCE_WORKER_RETRY_POLICY` budget per database call for host
/// `RESOURCE_EXHAUSTED` rejections before returning, rather than dropping
/// buffered writes early.
///
/// Sessions are not ordered per `uid`. Sessions for the same `uid` may persist
/// concurrently: the versioned metadata write rejects a stale version, and
/// `persist_database_with_policy` then rebases onto the latest blob and
/// retries, as it already must for writes from other enclaves and from
/// `SyncDatabase`. As a result, the mutations of the session whose write
/// commits last are applied last, regardless of the order in which the sessions
/// closed.
pub async fn run_persistence_service(
    mut rx: mpsc::UnboundedReceiver<UserSessionContext>,
    metrics: Arc<Metrics>,
) {
    info!("Persistence service started");
    let slots = PersistSlots::new();
    let mut persisting_tasks: JoinSet<()> = JoinSet::new();
    let mut rx_open = true;

    // Stay alive while:
    // 1. `rx_open`: the channel is open, even when idle (0 tasks in
    //    `persisting_tasks`).
    // 2. `!persisting_tasks.is_empty()`: save tasks are still running and must not
    //    be aborted.
    // Exits only when the channel closes AND all saves have drained.
    while rx_open || !persisting_tasks.is_empty() {
        tokio::select! {
            biased;
            (maybe_ctx, permit) = recv_when_slot_free(&mut rx, &slots.semaphore), if rx_open => {
                match maybe_ctx {
                    Some(user_context) => {
                        info!("Persistence service received a session to save");
                        slots.record_queue_size(rx.len(), &metrics);
                        let metrics = metrics.clone();
                        let slots = slots.clone();
                        persisting_tasks.spawn(async move {
                            let slot = slots.claim(permit, &metrics).await;
                            persist_one_session(user_context, metrics, slot).await;
                        });
                    }
                    None => rx_open = false,
                }
            }
            Some(join_result) = persisting_tasks.join_next(), if !persisting_tasks.is_empty() => {
                if let Err(join_error) = join_result {
                    metrics.inc_db_persist_failures();
                    error!("Persistence task panicked or was cancelled: {join_error:?}");
                }
            }
        }
    }
    info!("Persistence service finished");
}

/// Waits for a free worker slot, then receives the next session and claims the
/// slot for it.
///
/// The slot isn't held while waiting on `rx`, so an idle coordinator never
/// keeps a session that is resuming after a lock wait from its slot. If that
/// session takes the slot first, the returned permit is `None` and the new
/// session's task waits for the next free slot. Cancel-safe.
async fn recv_when_slot_free(
    rx: &mut mpsc::UnboundedReceiver<UserSessionContext>,
    slots: &Arc<Semaphore>,
) -> (Option<UserSessionContext>, Option<OwnedSemaphorePermit>) {
    drop(slots.acquire().await.expect("persist slots are never closed"));
    let maybe_ctx = rx.recv().await;
    (maybe_ctx, slots.clone().try_acquire_owned().ok())
}

#[cfg(test)]
mod tests {
    use std::{net::SocketAddr, sync::atomic::Ordering};

    use external_db_client::BlobId;
    use private_memory_test_database_server_lib::service::{
        LockState, SealedMemoryDatabaseServiceTestImpl,
    };
    use sealed_memory_rust_proto::oak::private_memory::{
        AddMemoryRequest, DataBlob, DeleteMemoryRequest, GetMemoryByIdRequest, Memory,
        ReadMetadataBlobStreamResponse, read_metadata_blob_stream_response,
    };
    use tonic::Code;
    use zeroize::Zeroizing;

    use super::*;
    use crate::{
        dek::{create_plain_text_user_info, generate_dek, reencrypt_into_copies, wrap_dek},
        handler::SealedMemorySessionHandler,
        test_util::{
            add_tagged, connect_handler, connect_handler_with_metrics, key_sync_request,
            memory_with_tag, registration_request, start_test_db, start_test_db_with_lock_state,
            start_test_db_with_service, tags_of,
        },
    };

    type TestMetrics = metrics_testing::TestMetrics<Metrics>;

    /// A `RESOURCE_EXHAUSTED` retry policy that retries quickly, so that tests
    /// don't wait for long.
    const FAST_RETRY_POLICY: ResourceExhaustedRetryPolicy = TEST_RETRY_POLICY;

    fn test_metrics() -> TestMetrics {
        TestMetrics::new(Metrics::new)
    }

    fn resource_exhausted_retries(harness: &TestMetrics) -> u64 {
        harness.collect().counter("db_resource_exhausted_retries", &[])
    }

    /// Persists like the background worker, but with `policy` for
    /// `RESOURCE_EXHAUSTED` rejections, and without holding a worker slot.
    async fn persist_database(
        user_context: &mut UserSessionContext,
        metrics: &Metrics,
        policy: ResourceExhaustedRetryPolicy,
    ) -> anyhow::Result<()> {
        persist_database_with_policy(
            user_context,
            metrics,
            policy,
            LockWaitPolicy::for_background_persist(),
            None,
        )
        .await
    }

    /// Registers and key-syncs `pm_uid` against the test database at
    /// `db_addr`, and adds a memory, so that the session's database has
    /// changes to persist. Returns the session.
    async fn session_with_changes(
        db_addr: SocketAddr,
        metrics: Arc<Metrics>,
        pm_uid: &str,
    ) -> UserSessionContext {
        // The handler hands its session to the persistence worker when it is
        // dropped, unless the session has been taken from it, as below.
        let (handler, _persistence_rx) = connect_handler_with_metrics(db_addr, metrics);
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        handler
            .add_memory_handler(AddMemoryRequest { memory: Some(memory_with_tag("tag")) })
            .await
            .unwrap();
        let session = handler.session_context().await.take().unwrap();
        assert!(session.database.changed());
        session
    }

    fn histogram_count_and_sum(harness: &TestMetrics, name: &str) -> (u64, u64) {
        let snapshot = harness.collect();
        if !snapshot.names().contains(name) {
            return (0, 0);
        }
        let point = snapshot.histogram(name, &[]);
        (point.count, point.sum)
    }

    fn fast_policy(max_wait: Duration) -> LockWaitPolicy {
        LockWaitPolicy {
            max_wait,
            first_delay: Duration::from_millis(1),
            max_delay: Duration::from_millis(4),
        }
    }

    #[test]
    fn retry_delay_doubles_up_to_the_cap() {
        let policy = LockWaitPolicy::for_background_persist();
        let ceilings_secs = [2, 4, 8, 16, 32, 60, 60, 60];
        for (conflicts, ceiling_secs) in (1..).zip(ceilings_secs) {
            let ceiling = Duration::from_secs(ceiling_secs);
            for _ in 0..20 {
                let delay = policy.retry_delay(conflicts);
                assert!(
                    (ceiling / 2..=ceiling).contains(&delay),
                    "delay {delay:?} after conflict {conflicts} is outside [{:?}, {ceiling:?}]",
                    ceiling / 2
                );
            }
        }
        assert!(policy.retry_delay(u32::MAX) <= policy.max_delay);
        assert!(policy.retry_delay(0) <= policy.first_delay);
    }

    #[test]
    fn background_wait_budget_is_spent_on_few_retries() {
        let policy = LockWaitPolicy::for_background_persist();
        let mut waited = Duration::ZERO;
        let mut retries = 0;
        while waited < policy.max_wait {
            retries += 1;
            waited += policy.retry_delay(retries).min(policy.max_wait - waited);
        }
        assert!(retries <= 35, "a row locked for {waited:?} was retried {retries} times");
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn lock_conflict_does_not_consume_the_rebase_budget() {
        let lock_state = LockState::new();
        let db_addr = start_test_db_with_lock_state(lock_state.clone()).await;
        let pm_uid = "lock_wait_survivor_user";

        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        let memory_id = handler
            .add_memory_handler(AddMemoryRequest { memory: Some(memory_with_tag("survivor")) })
            .await
            .unwrap()
            .id;

        lock_state.lock(pm_uid).await;
        let releaser = {
            let lock_state = lock_state.clone();
            let pm_uid = pm_uid.to_string();
            tokio::spawn(async move {
                while lock_state.rejections() <= MAX_RETRY_ATTEMPTS {
                    tokio::time::sleep(Duration::from_millis(1)).await;
                }
                lock_state.unlock(&pm_uid).await;
            })
        };

        {
            let mut guard = handler.session_context().await;
            let user_context = guard.as_mut().unwrap();
            persist_database_with_policy(
                user_context,
                &harness.metrics,
                FAST_RETRY_POLICY,
                fast_policy(Duration::from_secs(60)),
                None,
            )
            .await
            .expect("persist should outlast the lock, not burn the rebase budget");
        }
        releaser.await.unwrap();
        assert!(
            lock_state.rejections() > MAX_RETRY_ATTEMPTS,
            "test did not actually exceed the rebase budget: only {} refusals",
            lock_state.rejections(),
        );

        assert_eq!(
            harness.collect().counter("db_persist_lock_conflict_count", &[]),
            lock_state.rejections()
        );
        assert_eq!(histogram_count_and_sum(&harness, "db_persist_attempts"), (1, 1));
        assert_eq!(histogram_count_and_sum(&harness, "db_persist_lock_wait_latency").0, 1);

        let (reader, _persistence_rx) = connect_handler(db_addr);
        reader.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        let fetched = reader
            .get_memory_by_id_handler(GetMemoryByIdRequest {
                id: memory_id.clone(),
                result_mask: None,
            })
            .await
            .unwrap();
        assert!(fetched.success, "memory {memory_id} was lost across the lock wait");
        let fetched = fetched.memory.unwrap();
        assert_eq!(fetched.id, memory_id);
        assert_eq!(fetched.tags, vec!["survivor".to_string()]);
    }

    /// Background sessions waiting out a locked row give up their worker slots,
    /// so they don't stall another user's session.
    #[tokio::test(flavor = "multi_thread")]
    async fn sessions_waiting_on_a_lock_free_their_slots() {
        let lock_state = LockState::new();
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl {
            lock_state: lock_state.clone(),
            ..Default::default()
        });
        let db_addr = start_test_db_with_service(service.clone()).await;
        let harness = test_metrics();
        let locked_uid = "slot_locked_user";
        let free_uid = "slot_free_user";

        let mut locked_memories = Vec::new();
        let mut locked_contexts = Vec::new();
        for i in 0..MAX_CONCURRENT_PERSISTS {
            let (handler, _persistence_rx) =
                connect_handler_with_metrics(db_addr, harness.metrics.clone());
            if i == 0 {
                handler.user_registration_handler(registration_request(locked_uid)).await.unwrap();
            }
            handler.key_sync_handler(key_sync_request(locked_uid, None)).await.unwrap();
            let tag = format!("locked_{i}");
            let id = handler
                .add_memory_handler(AddMemoryRequest { memory: Some(memory_with_tag(&tag)) })
                .await
                .unwrap()
                .id;
            locked_memories.push((id, tag));
            locked_contexts.push(handler.session_context().await.take().unwrap());
        }
        let (free_handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        free_handler.user_registration_handler(registration_request(free_uid)).await.unwrap();
        free_handler.key_sync_handler(key_sync_request(free_uid, None)).await.unwrap();
        free_handler
            .add_memory_handler(AddMemoryRequest { memory: Some(memory_with_tag("free")) })
            .await
            .unwrap();
        let free_context = free_handler.session_context().await.take().unwrap();

        lock_state.lock(locked_uid).await;
        let (persistence_tx, persistence_rx) = mpsc::unbounded_channel();
        let worker = tokio::spawn(run_persistence_service(persistence_rx, harness.metrics.clone()));
        for context in locked_contexts {
            persistence_tx.send(context).unwrap();
        }
        let deadline = Instant::now() + Duration::from_secs(30);
        while lock_state.rejections() < MAX_CONCURRENT_PERSISTS as u64 {
            assert!(Instant::now() < deadline, "locked sessions never tried to write");
            tokio::time::sleep(Duration::from_millis(5)).await;
        }

        persistence_tx.send(free_context).unwrap();
        while service.get_metdata_blob_inner(free_uid).await.is_none() {
            assert!(Instant::now() < deadline, "locked sessions stalled another user's persist");
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
        assert!(service.get_metdata_blob_inner(locked_uid).await.is_none());
        // The sessions waiting out the lock still count as queued.
        let queue_size = || harness.collect().gauge("db_persist_queue_size", &[]);
        while queue_size() != MAX_CONCURRENT_PERSISTS as u64 {
            assert!(Instant::now() < deadline, "queue size {} while sessions wait", queue_size());
            tokio::time::sleep(Duration::from_millis(5)).await;
        }

        lock_state.unlock(locked_uid).await;
        // Keep the queue open until every session persisted: closing it while
        // a write is still in flight against the locked row would cut that
        // session's wait short.
        let all_sessions = MAX_CONCURRENT_PERSISTS as u64 + 1;
        while histogram_count_and_sum(&harness, "db_persist_attempts").0 < all_sessions {
            assert!(
                Instant::now() < deadline + Duration::from_secs(60),
                "locked sessions never persisted after the lock was released"
            );
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
        drop(persistence_tx);
        tokio::time::timeout(Duration::from_secs(60), worker)
            .await
            .expect("locked sessions never persisted after the lock was released")
            .unwrap();
        assert_eq!(harness.collect().counter("db_persist_failures", &[]), 0);
        assert_eq!(queue_size(), 0);
        let (reader, _persistence_rx) = connect_handler(db_addr);
        reader.key_sync_handler(key_sync_request(locked_uid, None)).await.unwrap();
        for (id, tag) in locked_memories {
            let fetched = reader
                .get_memory_by_id_handler(GetMemoryByIdRequest { id, result_mask: None })
                .await
                .unwrap();
            assert!(fetched.success, "memory {tag} was lost");
            assert_eq!(fetched.memory.unwrap().tags, vec![tag]);
        }
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn lock_held_forever_fails_after_the_wait_budget() {
        let lock_state = LockState::new();
        let db_addr = start_test_db_with_lock_state(lock_state.clone()).await;
        let pm_uid = "lock_wait_timeout_user";

        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        handler
            .add_memory_handler(AddMemoryRequest { memory: Some(memory_with_tag("doomed")) })
            .await
            .unwrap();

        lock_state.lock(pm_uid).await;

        let max_wait = Duration::from_millis(200);
        let started = Instant::now();
        let error = {
            let mut guard = handler.session_context().await;
            let user_context = guard.as_mut().unwrap();
            persist_database_with_policy(
                user_context,
                &harness.metrics,
                FAST_RETRY_POLICY,
                fast_policy(max_wait),
                None,
            )
            .await
            .expect_err("a permanently locked row must not persist")
        };
        let elapsed = started.elapsed();

        assert!(elapsed >= max_wait, "gave up after only {elapsed:?}, budget was {max_wait:?}");
        let error = format!("{error}");
        assert!(error.contains("locked"), "unhelpful lock-wait error: {error}");
        assert!(lock_state.rejections() > 0);

        assert_eq!(
            harness.collect().counter("db_persist_lock_conflict_count", &[]),
            lock_state.rejections()
        );
        let (count, waited_ms) = histogram_count_and_sum(&harness, "db_persist_lock_wait_latency");
        assert_eq!(count, 1);
        assert!(waited_ms >= max_wait.as_millis() as u64, "recorded wait {waited_ms}ms");
        assert_eq!(histogram_count_and_sum(&harness, "db_persist_attempts"), (0, 0));
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn lock_wait_budget_counts_write_rpc_time() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let db_addr = start_test_db_with_service(service.clone()).await;
        let pm_uid = "lock_wait_wall_clock_user";

        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        handler
            .add_memory_handler(AddMemoryRequest { memory: Some(memory_with_tag("slow")) })
            .await
            .unwrap();

        service.lock_state.lock(pm_uid).await;
        let max_wait = Duration::from_millis(300);
        let retry_delay = Duration::from_millis(100);
        let policy = LockWaitPolicy { max_wait, first_delay: retry_delay, max_delay: retry_delay };
        let stall_second_write = async {
            let (first, release_first) = service.hold_next_metadata_write().await;
            first.await.unwrap();
            let (second, release_second) = service.hold_next_metadata_write().await;
            release_first.send(()).unwrap();
            second.await.unwrap();
            tokio::time::sleep(max_wait).await;
            release_second.send(()).unwrap();
        };
        let persist = async {
            let mut guard = handler.session_context().await;
            let user_context = guard.as_mut().unwrap();
            persist_database_with_policy(
                user_context,
                &harness.metrics,
                FAST_RETRY_POLICY,
                policy,
                None,
            )
            .await
        };
        let (result, ()) = tokio::time::timeout(Duration::from_secs(10), async {
            tokio::join!(persist, stall_second_write)
        })
        .await
        .expect("a held write never arrived");

        let error = result.expect_err("a locked row must not persist");
        assert!(error.is::<RowLocked>(), "expected RowLocked, got {error:?}");
        assert_eq!(service.lock_state.rejections(), 2, "the stalled write should end the wait");
        let (count, waited_ms) = histogram_count_and_sum(&harness, "db_persist_lock_wait_latency");
        assert_eq!(count, 1);
        assert!(waited_ms >= max_wait.as_millis() as u64, "recorded wait {waited_ms}ms");
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn persist_without_contention_never_waits() {
        let lock_state = LockState::new();
        let db_addr = start_test_db_with_lock_state(lock_state.clone()).await;
        let pm_uid = "lock_wait_uncontended_user";

        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        handler
            .add_memory_handler(AddMemoryRequest { memory: Some(memory_with_tag("uncontended")) })
            .await
            .unwrap();

        {
            let mut guard = handler.session_context().await;
            let user_context = guard.as_mut().unwrap();
            persist_database_with_policy(
                user_context,
                &harness.metrics,
                FAST_RETRY_POLICY,
                fast_policy(Duration::from_secs(60)),
                None,
            )
            .await
            .unwrap();
        }
        assert_eq!(lock_state.rejections(), 0);
        assert_eq!(harness.collect().counter("db_persist_lock_conflict_count", &[]), 0);
        assert_eq!(histogram_count_and_sum(&harness, "db_persist_lock_wait_latency"), (0, 0));
        assert_eq!(histogram_count_and_sum(&harness, "db_persist_attempts"), (1, 1));
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn sync_on_locked_row_gives_up_with_row_locked() {
        let lock_state = LockState::new();
        let db_addr = start_test_db_with_lock_state(lock_state.clone()).await;
        let pm_uid = "sync_locked_user";

        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        handler
            .add_memory_handler(AddMemoryRequest { memory: Some(memory_with_tag("sync")) })
            .await
            .unwrap();

        lock_state.lock(pm_uid).await;
        let error = {
            let mut guard = handler.session_context().await;
            let user_context = guard.as_mut().unwrap();
            sync_persist_database_with_policy(
                user_context,
                &harness.metrics,
                FAST_RETRY_POLICY,
                fast_policy(Duration::from_millis(50)),
            )
            .await
            .expect_err("a locked row must not persist")
        };
        assert!(error.is::<RowLocked>(), "expected RowLocked, got {error:?}");
        assert_eq!(
            harness.collect().counter("db_persist_lock_conflict_count", &[]),
            lock_state.rejections()
        );
        assert_eq!(histogram_count_and_sum(&harness, "db_persist_lock_wait_latency").0, 1);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn persistence_service_waits_for_row_lock_and_records_metrics() {
        let lock_state = LockState::new();
        let db_addr = start_test_db_with_lock_state(lock_state.clone()).await;
        let pm_uid = "service_lock_wait_user";

        let harness = test_metrics();
        let (handler, persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        handler
            .add_memory_handler(AddMemoryRequest { memory: Some(memory_with_tag("queued")) })
            .await
            .unwrap();

        lock_state.lock(pm_uid).await;
        let releaser = {
            let lock_state = lock_state.clone();
            let pm_uid = pm_uid.to_string();
            tokio::spawn(async move {
                while lock_state.rejections() == 0 {
                    tokio::time::sleep(Duration::from_millis(1)).await;
                }
                lock_state.unlock(&pm_uid).await;
            })
        };

        drop(handler);
        run_persistence_service(persistence_rx, harness.metrics.clone()).await;
        releaser.await.unwrap();

        assert_eq!(harness.collect().counter("db_persist_lock_conflict_count", &[]), 1);
        let (count, waited_ms) = histogram_count_and_sum(&harness, "db_persist_lock_wait_latency");
        assert_eq!(count, 1);
        // The first retry comes after half to all of the 2s first delay.
        assert!(waited_ms >= 1_000, "recorded wait {waited_ms}ms");
        assert_eq!(histogram_count_and_sum(&harness, "db_persist_attempts"), (1, 1));
        assert_eq!(harness.collect().gauge("db_persist_queue_size", &[]), 0);
    }

    async fn rotate_dek_externally(db_addr: SocketAddr, pm_uid: &str) -> Zeroizing<Vec<u8>> {
        let (rotator, _persistence_rx) = connect_handler(db_addr);
        rotator.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        let mut guard = rotator.session_context().await;
        let ctx = guard.as_mut().unwrap();

        let dek_new = generate_dek();
        let blobs = ctx.database.get_all_memory_and_blob_ids().unwrap();
        let reencryption =
            reencrypt_into_copies(&mut ctx.database, &blobs, &dek_new, || Ok(())).await.unwrap();
        reencryption.repoint(&mut ctx.database).unwrap();
        let encrypted_info = ctx.database.export().unwrap().encrypted_info.unwrap();
        let metadata = encrypt_database(&encrypted_info, &dek_new).unwrap();
        let wrapped = wrap_dek(&dek_new, &ctx.kek).unwrap();
        let plain_text_info =
            create_plain_text_user_info(Some(ctx.database.key_derivation_info().clone()), wrapped);
        let result = ctx
            .database_service_client
            .add_metadata_blob_stream_with_lock(
                &ctx.uid,
                &EncryptedMetadataBlob {
                    encrypted_data_blob: Some(metadata),
                    version: ctx.database_version.clone(),
                },
                ctx.database.calculate_coarsened_blanket_ttl(),
                "",
                Some(DataBlob { id: ctx.uid.clone(), blob: plain_text_info.encode_to_vec() }),
            )
            .await
            .unwrap();
        assert!(matches!(result, MetadataPersistResult::Succeeded { .. }), "{result:?}");
        *guard = None;
        dek_new
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn persist_after_external_dek_rotation_keeps_pending_changes() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let db_addr = start_test_db_with_service(service.clone()).await;
        let pm_uid = "clean_rebase_user";
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        let untouched = add_tagged(&handler, "untouched").await;
        let upserted = add_tagged(&handler, "before-upsert").await;
        let deleted = add_tagged(&handler, "to-delete").await;
        {
            let mut guard = handler.session_context().await;
            persist_database(guard.as_mut().unwrap(), &harness.metrics, FAST_RETRY_POLICY)
                .await
                .unwrap();
        }

        let added = add_tagged(&handler, "added-after").await;
        {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            ctx.database
                .add_memory(Memory { id: upserted.clone(), ..memory_with_tag("after-upsert") })
                .await
                .unwrap();
        }
        handler
            .delete_memory_handler(DeleteMemoryRequest { ids: vec![deleted.clone()] })
            .await
            .unwrap();

        let dek_new = rotate_dek_externally(db_addr, pm_uid).await;

        {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            let pending_before: Vec<BlobId> = ctx
                .database
                .get_pending_add_memory_blob_ids()
                .unwrap()
                .into_iter()
                .map(|(_, blob_id)| blob_id)
                .collect();
            assert!(!pending_before.is_empty());
            persist_database(ctx, &harness.metrics, FAST_RETRY_POLICY)
                .await
                .expect("persist should move onto the rotated DEK");
            assert_eq!(*ctx.dek, *dek_new);
            let blobs = service.database.lock().await;
            for blob_id in &pending_before {
                assert!(!blobs.contains_key(blob_id), "old pending blob {blob_id} was kept");
            }
        }
        assert_eq!(harness.collect().counter("db_decryption_failures", &[]), 0);

        let (reader, _persistence_rx) = connect_handler(db_addr);
        reader.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        assert_eq!(tags_of(&reader, &untouched).await, Some(vec!["untouched".to_string()]));
        assert_eq!(tags_of(&reader, &upserted).await, Some(vec!["after-upsert".to_string()]));
        assert_eq!(tags_of(&reader, &added).await, Some(vec!["added-after".to_string()]));
        assert_eq!(tags_of(&reader, &deleted).await, None);
    }

    /// A rebase that fetched the blob just before another rotation committed
    /// moves the session onto the newest DEK and fetches the blob again,
    /// instead of counting a decryption failure and failing the persist.
    #[tokio::test(flavor = "multi_thread")]
    async fn rebase_refetches_a_blob_that_predates_the_stored_dek() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let db_addr = start_test_db_with_service(service.clone()).await;
        let pm_uid = "two_rotations_user";
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        let persisted = add_tagged(&handler, "persisted").await;
        {
            let mut guard = handler.session_context().await;
            persist_database(guard.as_mut().unwrap(), &harness.metrics, FAST_RETRY_POLICY)
                .await
                .unwrap();
        }
        let pending = add_tagged(&handler, "pending").await;

        rotate_dek_externally(db_addr, pm_uid).await;
        let stale_blob = service.get_metdata_blob_inner(pm_uid).await.unwrap();
        let dek_newest = rotate_dek_externally(db_addr, pm_uid).await;
        // The session's first fetch gets the first rotation's blob, as if the
        // second rotation committed right after that fetch.
        *service.next_metadata_stream_reply.lock().await =
            Some(vec![ReadMetadataBlobStreamResponse {
                response: Some(read_metadata_blob_stream_response::Response::MetadataBlob(
                    stale_blob,
                )),
            }]);

        {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            persist_database(ctx, &harness.metrics, FAST_RETRY_POLICY)
                .await
                .expect("persist should follow both rotations");
            assert_eq!(*ctx.dek, *dek_newest);
        }
        assert!(service.next_metadata_stream_reply.lock().await.is_none());
        assert_eq!(harness.collect().counter("db_decryption_failures", &[]), 0);

        let (reader, _persistence_rx) = connect_handler(db_addr);
        reader.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        assert_eq!(tags_of(&reader, &persisted).await, Some(vec!["persisted".to_string()]));
        assert_eq!(tags_of(&reader, &pending).await, Some(vec!["pending".to_string()]));
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn failed_switch_discards_its_copies_and_keeps_the_session() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let db_addr = start_test_db_with_service(service.clone()).await;
        let pm_uid = "failed_switch_user";
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        add_tagged(&handler, "persisted").await;
        {
            let mut guard = handler.session_context().await;
            persist_database(guard.as_mut().unwrap(), &harness.metrics, FAST_RETRY_POLICY)
                .await
                .unwrap();
        }
        add_tagged(&handler, "pending-kept").await;
        let lost = add_tagged(&handler, "pending-lost").await;
        rotate_dek_externally(db_addr, pm_uid).await;

        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let lost_blob = ctx
            .database
            .get_pending_add_memory_blob_ids()
            .unwrap()
            .into_iter()
            .find(|(memory_id, _)| *memory_id == lost)
            .unwrap()
            .1;
        service.database.lock().await.remove(&lost_blob).unwrap();
        let blobs_before: std::collections::BTreeSet<String> =
            service.database.lock().await.keys().cloned().collect();
        let dek_before = ctx.dek.clone();
        let version_before = ctx.database_version.clone();
        let pending_before = ctx.database.get_pending_add_memory_blob_ids().unwrap();

        let error = persist_database(ctx, &harness.metrics, FAST_RETRY_POLICY)
            .await
            .expect_err("switch must fail");

        assert!(format!("{error:?}").contains("disappeared"), "{error:?}");
        assert_eq!(*ctx.dek, *dek_before);
        assert_eq!(ctx.database_version, version_before);
        assert_eq!(ctx.database.get_pending_add_memory_blob_ids().unwrap(), pending_before);
        let blobs_after: std::collections::BTreeSet<String> =
            service.database.lock().await.keys().cloned().collect();
        assert_eq!(blobs_after, blobs_before, "the copy of the surviving pending blob was kept");
        assert_eq!(harness.collect().counter("db_decryption_failures", &[]), 0);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn undecryptable_blob_under_the_same_dek_fails_without_touching_the_session() {
        let db_addr = start_test_db().await;
        let pm_uid = "undecryptable_blob_user";
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        add_tagged(&handler, "persisted").await;
        {
            let mut guard = handler.session_context().await;
            persist_database(guard.as_mut().unwrap(), &harness.metrics, FAST_RETRY_POLICY)
                .await
                .unwrap();
        }
        add_tagged(&handler, "pending").await;

        {
            let (other, _persistence_rx) = connect_handler(db_addr);
            other.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
            let mut guard = other.session_context().await;
            let ctx = guard.as_mut().unwrap();
            let encrypted_info = ctx.database.export().unwrap().encrypted_info.unwrap();
            let garbage = encrypt_database(&encrypted_info, &generate_dek()).unwrap();
            let result = ctx
                .database_service_client
                .add_metadata_blob_stream(
                    &ctx.uid,
                    &EncryptedMetadataBlob {
                        encrypted_data_blob: Some(garbage),
                        version: ctx.database_version.clone(),
                    },
                    ctx.database.calculate_coarsened_blanket_ttl(),
                )
                .await
                .unwrap();
            assert!(matches!(result, MetadataPersistResult::Succeeded { .. }), "{result:?}");
            *guard = None;
        }

        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let dek_before = ctx.dek.clone();
        let version_before = ctx.database_version.clone();
        let pending_before = ctx.database.get_pending_add_memory_blob_ids().unwrap();

        let error = persist_database(ctx, &harness.metrics, FAST_RETRY_POLICY)
            .await
            .expect_err("corrupt blob must not be rebased onto");

        assert!(format!("{error:?}").contains("stored DEK is the session DEK"), "{error:?}");
        assert_eq!(*ctx.dek, *dek_before);
        assert_eq!(ctx.database_version, version_before);
        assert_eq!(ctx.database.get_pending_add_memory_blob_ids().unwrap(), pending_before);
        assert!(ctx.database.changed());
        assert_eq!(harness.collect().counter("db_decryption_failures", &[]), 1);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn blob_undecryptable_under_the_rotated_dek_counts_a_decryption_failure() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let db_addr = start_test_db_with_service(service.clone()).await;
        let pm_uid = "undecryptable_after_rotation_user";
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        add_tagged(&handler, "persisted").await;
        {
            let mut guard = handler.session_context().await;
            persist_database(guard.as_mut().unwrap(), &harness.metrics, FAST_RETRY_POLICY)
                .await
                .unwrap();
        }
        add_tagged(&handler, "pending").await;

        let dek_new = rotate_dek_externally(db_addr, pm_uid).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let encrypted_info = ctx.database.export().unwrap().encrypted_info.unwrap();
        let garbage = encrypt_database(&encrypted_info, &generate_dek()).unwrap();
        service.metadata_database.lock().await.get_mut(pm_uid).unwrap().data_blob =
            Some(DataBlob { id: pm_uid.to_string(), blob: garbage.encode_to_vec() });

        persist_database(ctx, &harness.metrics, FAST_RETRY_POLICY)
            .await
            .expect_err("a blob that is corrupt under the stored DEK must not be rebased onto");

        assert_eq!(*ctx.dek, *dek_new);
        assert_eq!(harness.collect().counter("db_decryption_failures", &[]), 1);
    }

    /// Only a `RESOURCE_EXHAUSTED` status is a host rejection.
    #[test]
    fn is_resource_exhausted_checks_status_code() {
        assert!(is_resource_exhausted(&anyhow::Error::from(tonic::Status::resource_exhausted(
            "host memory pressure"
        ))));
        assert!(!is_resource_exhausted(&anyhow::Error::from(tonic::Status::unavailable("down"))));
        assert!(!is_resource_exhausted(&anyhow::anyhow!("RESOURCE_EXHAUSTED")));
    }

    /// A metadata write that the host rejects with `RESOURCE_EXHAUSTED` is
    /// retried until it succeeds, without counting as a persist attempt.
    #[tokio::test(flavor = "multi_thread")]
    async fn persist_retries_resource_exhausted_writes() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let harness = test_metrics();
        let pm_uid = "resource_exhausted_write_user";
        let mut session = session_with_changes(
            start_test_db_with_service(service.clone()).await,
            harness.metrics.clone(),
            pm_uid,
        )
        .await;
        service.fail_next_metadata_writes(Code::ResourceExhausted, 3).await;

        persist_database(&mut session, &harness.metrics, FAST_RETRY_POLICY).await.unwrap();

        assert_eq!(service.metadata_write_calls.load(Ordering::SeqCst), 4);
        let payloads = service.metadata_write_payloads.lock().await;
        assert_eq!(payloads.len(), 4);
        assert!(payloads.iter().all(|payload| *payload == payloads[0]));
        assert_eq!(resource_exhausted_retries(&harness), 3);
        assert!(service.get_metdata_blob_inner(pm_uid).await.is_some());
        assert!(!session.database.changed());
        // There was no version conflict, so it was persisted on the first
        // attempt.
        assert_eq!(harness.collect().histogram("db_persist_attempts", &[]).sum, 1);
    }

    /// Once the retry budget is spent, the rejection is returned, and the
    /// changes stay unpersisted in the session.
    #[tokio::test(flavor = "multi_thread")]
    async fn persist_fails_when_resource_exhausted_budget_is_spent() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let harness = test_metrics();
        let pm_uid = "resource_exhausted_budget_user";
        let mut session = session_with_changes(
            start_test_db_with_service(service.clone()).await,
            harness.metrics.clone(),
            pm_uid,
        )
        .await;
        service.fail_next_metadata_writes(Code::ResourceExhausted, 1000).await;

        let policy = ResourceExhaustedRetryPolicy {
            total_budget: Duration::from_millis(100),
            ..FAST_RETRY_POLICY
        };
        let start = Instant::now();
        let error = persist_database(&mut session, &harness.metrics, policy).await.unwrap_err();

        assert!(is_resource_exhausted(&error), "{error:?}");
        // The budget bounds the time spent retrying (plus the final attempt).
        assert!(start.elapsed() < Duration::from_secs(5), "{:?}", start.elapsed());
        let writes = service.metadata_write_calls.load(Ordering::SeqCst) as u64;
        assert!(writes > 1, "{writes}");
        assert_eq!(resource_exhausted_retries(&harness), writes - 1);
        assert!(service.get_metdata_blob_inner(pm_uid).await.is_none());
        assert!(session.database.changed());
    }

    /// Other host errors are not retried.
    #[tokio::test(flavor = "multi_thread")]
    async fn persist_does_not_retry_other_errors() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let harness = test_metrics();
        let mut session = session_with_changes(
            start_test_db_with_service(service.clone()).await,
            harness.metrics.clone(),
            "unavailable_write_user",
        )
        .await;
        service.fail_next_metadata_writes(Code::Unavailable, 1).await;

        let error =
            persist_database(&mut session, &harness.metrics, FAST_RETRY_POLICY).await.unwrap_err();

        assert_eq!(error.downcast_ref::<tonic::Status>().unwrap().code(), Code::Unavailable);
        assert_eq!(service.metadata_write_calls.load(Ordering::SeqCst), 1);
        assert_eq!(resource_exhausted_retries(&harness), 0);
        assert!(session.database.changed());
    }

    /// SyncDatabase retries both its read (pull) and its write (push) when the
    /// host rejects them with `RESOURCE_EXHAUSTED`, each with its own budget.
    #[tokio::test(flavor = "multi_thread")]
    async fn sync_retries_resource_exhausted_reads_and_writes() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let harness = test_metrics();
        let pm_uid = "resource_exhausted_sync_user";
        let mut session = session_with_changes(
            start_test_db_with_service(service.clone()).await,
            harness.metrics.clone(),
            pm_uid,
        )
        .await;
        let reads_before = service.metadata_read_calls.load(Ordering::SeqCst);
        let writes_before = service.metadata_write_calls.load(Ordering::SeqCst);
        service.fail_next_metadata_reads(Code::ResourceExhausted, 2).await;
        service.fail_next_metadata_writes(Code::ResourceExhausted, 2).await;

        sync_persist_database_with_policy(
            &mut session,
            &harness.metrics,
            FAST_RETRY_POLICY,
            LockWaitPolicy::for_sync(),
        )
        .await
        .unwrap();

        assert_eq!(service.metadata_read_calls.load(Ordering::SeqCst) - reads_before, 3);
        assert_eq!(service.metadata_write_calls.load(Ordering::SeqCst) - writes_before, 3);
        assert_eq!(resource_exhausted_retries(&harness), 4);
        assert!(service.get_metdata_blob_inner(pm_uid).await.is_some());
        assert!(!session.database.changed());
    }

    /// Each database call gets its own retry budget: a read retry doesn't use
    /// up the budget of the write that follows it.
    #[tokio::test(flavor = "multi_thread")]
    async fn sync_gives_each_database_call_its_own_budget() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let harness = test_metrics();
        let pm_uid = "resource_exhausted_per_call_user";
        let mut session = session_with_changes(
            start_test_db_with_service(service.clone()).await,
            harness.metrics.clone(),
            pm_uid,
        )
        .await;
        service.fail_next_metadata_reads(Code::ResourceExhausted, 1).await;
        service.fail_next_metadata_writes(Code::ResourceExhausted, 1).await;

        // Every sleep is between 50ms and 100ms, so each call has budget for
        // exactly one retry. A budget shared by the read and the write would
        // run out at the write's retry: by then, the read's sleep, the calls
        // in between, and the write's sleep add up to more than 101ms.
        let one_retry_per_call = ResourceExhaustedRetryPolicy {
            initial_backoff: Duration::from_millis(100),
            max_backoff: Duration::from_millis(100),
            total_budget: Duration::from_millis(101),
        };
        sync_persist_database_with_policy(
            &mut session,
            &harness.metrics,
            one_retry_per_call,
            LockWaitPolicy::for_sync(),
        )
        .await
        .unwrap();

        assert_eq!(resource_exhausted_retries(&harness), 2);
        assert!(service.get_metdata_blob_inner(pm_uid).await.is_some());
    }

    /// The persistence worker rides out `RESOURCE_EXHAUSTED` rejections with
    /// its production policy instead of dropping the session.
    #[tokio::test(flavor = "multi_thread")]
    async fn persistence_service_retries_resource_exhausted_writes() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let harness = test_metrics();
        let pm_uid = "resource_exhausted_worker_user";
        let session = session_with_changes(
            start_test_db_with_service(service.clone()).await,
            harness.metrics.clone(),
            pm_uid,
        )
        .await;
        service.fail_next_metadata_writes(Code::ResourceExhausted, 2).await;

        let (persistence_tx, persistence_rx) = mpsc::unbounded_channel();
        persistence_tx.send(session).unwrap();
        drop(persistence_tx);
        run_persistence_service(persistence_rx, harness.metrics.clone()).await;

        assert_eq!(service.metadata_write_calls.load(Ordering::SeqCst), 3);
        assert_eq!(resource_exhausted_retries(&harness), 2);
        assert_eq!(harness.collect().counter("db_persist_failures", &[]), 0);
        assert!(service.get_metdata_blob_inner(pm_uid).await.is_some());
    }

    /// A registered, key-synced session against `service`.
    struct LockTestSession {
        db_addr: SocketAddr,
        handler: SealedMemorySessionHandler,
        harness: TestMetrics,
        _persistence_rx: mpsc::UnboundedReceiver<UserSessionContext>,
    }

    async fn registered_session(
        service: &Arc<SealedMemoryDatabaseServiceTestImpl>,
        pm_uid: &str,
    ) -> LockTestSession {
        let db_addr = start_test_db_with_service(service.clone()).await;
        let harness = test_metrics();
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        LockTestSession { db_addr, handler, harness, _persistence_rx }
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn persist_under_lock_commits_and_adopts_the_new_version() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let pm_uid = "persist_under_lock_user";
        let LockTestSession { db_addr, handler, harness, _persistence_rx: _rx } =
            registered_session(&service, pm_uid).await;
        let memory = add_tagged(&handler, "locked").await;

        {
            let mut guard = handler.session_context().await;
            let ctx = guard.as_mut().unwrap();
            let lock = ctx
                .database_service_client
                .acquire_unencrypted_blob_lock(&ctx.uid, Duration::from_secs(60))
                .await
                .unwrap();

            let reads_before = service.metadata_read_calls.load(Ordering::SeqCst);

            persist_under_lock(ctx, &harness.metrics, &lock.lock_token).await.unwrap();

            assert!(!ctx.database.changed());
            let stored_version = service.metadata_database.lock().await[pm_uid].version.clone();
            assert_eq!(ctx.database_version, stored_version);
            // The host reported the committed version, so it wasn't read back.
            assert_eq!(service.metadata_read_calls.load(Ordering::SeqCst), reads_before);
            assert_eq!(service.lock_state.held_token(pm_uid).await, Some(lock.lock_token));
        }
        let (reader, _reader_rx) = connect_handler(db_addr);
        reader.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        assert_eq!(tags_of(&reader, &memory).await, Some(vec!["locked".to_string()]));
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn persist_under_a_lock_held_by_someone_else_fails_with_row_lock_lost() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let pm_uid = "persist_under_lost_lock_user";
        let LockTestSession { handler, harness, _persistence_rx: _rx, .. } =
            registered_session(&service, pm_uid).await;
        add_tagged(&handler, "unsaved").await;
        service.lock_state.lock(pm_uid).await;

        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let error = persist_under_lock(ctx, &harness.metrics, "stale-token").await.unwrap_err();

        assert!(error.is::<RowLockLost>(), "{error:?}");
        assert!(ctx.database.changed());
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn version_conflict_under_the_lock_fails_with_row_lock_lost() {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let pm_uid = "persist_under_lock_conflict_user";
        let LockTestSession { handler, harness, _persistence_rx: _rx, .. } =
            registered_session(&service, pm_uid).await;
        add_tagged(&handler, "persisted").await;
        persist_database(
            handler.session_context().await.as_mut().unwrap(),
            &harness.metrics,
            FAST_RETRY_POLICY,
        )
        .await
        .unwrap();
        add_tagged(&handler, "unsaved").await;

        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let lock = ctx
            .database_service_client
            .acquire_unencrypted_blob_lock(&ctx.uid, Duration::from_secs(60))
            .await
            .unwrap();
        ctx.database_version = "a version another writer replaced".to_string();
        let error = persist_under_lock(ctx, &harness.metrics, &lock.lock_token).await.unwrap_err();

        assert!(error.is::<RowLockLost>(), "{error:?}");
        assert!(ctx.database.changed());
    }
}
