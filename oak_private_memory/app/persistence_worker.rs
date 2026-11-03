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
use std::{sync::Arc, time::Duration};

use anyhow::Context;
use external_db_client::{DataBlobHandler, MetadataBlobRead, MetadataPersistResult};
use log::{error, info, warn};
use metrics::Metrics;
use oak_private_memory_database::encryption::{decrypt_database, encrypt_database};
use prost::Message;
use sealed_memory_rust_proto::{
    oak::private_memory::EncryptedMetadataBlob, prelude::v1::SyncDatabaseResponse,
};
use tokio::{sync::mpsc, task::JoinSet, time::Instant};

/// Maximum number of attempts to persist the database when its write hits a
/// version conflict. Retries of host `RESOURCE_EXHAUSTED` rejections don't
/// count towards this; each database call's retries are bounded by a
/// [`ResourceExhaustedRetryPolicy`] instead.
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
struct ResourceExhaustedRetryPolicy {
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
struct ResourceExhaustedBackoff {
    policy: ResourceExhaustedRetryPolicy,
    /// When the first rejection was seen, if any.
    first_rejection: Option<Instant>,
    /// The upper bound of the next sleep.
    next_backoff: Duration,
    /// The number of retries so far.
    retries: u64,
}

impl ResourceExhaustedBackoff {
    fn new(policy: ResourceExhaustedRetryPolicy) -> Self {
        Self { policy, first_rejection: None, next_backoff: policy.initial_backoff, retries: 0 }
    }

    /// Handles the `error` that a database call for `operation` failed with.
    ///
    /// If the host rejected the call with `RESOURCE_EXHAUSTED`, and the budget
    /// allows another attempt, sleeps and returns `Ok`: the caller should
    /// retry the call. Otherwise returns the error.
    async fn wait_to_retry(
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

/// Minimum number of optimizable (deleted/expired) documents before calling
/// Icing.Optimize. GetOptimizeInfo (~0.16ms) is called on every persist to
/// check, and Optimize (~1s) is only called when this threshold is exceeded.
pub(crate) const OPTIMIZE_DOC_THRESHOLD: i64 = 100;

use crate::context::UserSessionContext;

// Attempt to persist the database once.
// If there is a failure due to a version mismatch,
// Ok(MetadataPersistResult::RetryNeeded) will be returned. The caller should
// re-fetch the latest metadatablob and rebase the icing database and try again.
//
// The database is exported and encrypted once. If the host rejects the write
// with RESOURCE_EXHAUSTED, the same encrypted database is sent again, as far
// as `policy` allows.
async fn try_persist_database(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
    policy: ResourceExhaustedRetryPolicy,
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
            .add_metadata_blob_stream(
                &user_context.uid,
                &metadata_blob,
                coarsened_expiration_timestamp,
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

/// Fetch the latest remote blob and rebase the local database onto it.
///
/// If `require_blob` is true, a missing blob is an error (used on CAS retry,
/// after the write was rejected because the blob changed). If false, a missing
/// blob is silently skipped (used for SyncDatabase, where the user may not have
/// any persisted data yet), and the host skips sending the blob if it still has
/// the session's `database_version`.
///
/// Retries the fetch while the host rejects it with `RESOURCE_EXHAUSTED`, as
/// far as `policy` allows.
async fn pull_and_rebase(
    user_context: &mut UserSessionContext,
    require_blob: bool,
    metrics: &Metrics,
    policy: ResourceExhaustedRetryPolicy,
) -> anyhow::Result<()> {
    let coarsened_expiration_timestamp = user_context.database.calculate_coarsened_blanket_ttl();
    // Send the session's version, so that an unchanged blob isn't downloaded
    // again. On CAS retry the blob is known to have changed, so don't.
    let known_version = (!require_blob && !user_context.database_version.is_empty())
        .then_some(user_context.database_version.as_str());
    let mut backoff = ResourceExhaustedBackoff::new(policy);
    let (refreshed_blob, fetch_elapsed) = loop {
        let fetch_start = Instant::now();
        match user_context
            .database_service_client
            .get_metadata_blob_stream(
                &user_context.uid,
                coarsened_expiration_timestamp,
                known_version,
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
    let decrypted = decrypt_database(encrypted_data_blob, &user_context.dek)
        .inspect_err(|_| metrics.inc_db_decryption_failures())?;
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
    user_context.database_version = refreshed_blob.version;
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
/// according to [`SYNC_DATABASE_RETRY_POLICY`].
pub async fn sync_persist_database(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
) -> anyhow::Result<SyncDatabaseResponse> {
    sync_persist_database_with_policy(user_context, metrics, SYNC_DATABASE_RETRY_POLICY).await
}

async fn sync_persist_database_with_policy(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
    policy: ResourceExhaustedRetryPolicy,
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
    persist_database(user_context, metrics, policy).await?;

    Ok(SyncDatabaseResponse {})
}

async fn persist_one_session(mut user_context: UserSessionContext, metrics: Arc<Metrics>) {
    // Optimize is expensive (~1s for a 30MB database) and always rebuilds
    // the entire index. Use GetOptimizeInfo (~0.16ms) to check whether
    // there are enough deleted/expired documents to warrant optimization.
    if let Err(e) = maybe_optimize(&mut user_context.database, &metrics) {
        error!("optimizing database: {e:?}");
    }

    if let Err(e) =
        persist_database(&mut user_context, &metrics, PERSISTENCE_WORKER_RETRY_POLICY).await
    {
        metrics.inc_db_persist_failures();
        error!("Failed to persist database: {:?}", e);
    }
}

// Attempt to persist the database up to MAX_RETRY_ATTEMPTS times.
// Retries only occur when the write is rejected for a version conflict.
//
// Independently, database calls that the host rejects with RESOURCE_EXHAUSTED
// are retried as far as `policy` allows, without counting as attempts.
async fn persist_database(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
    policy: ResourceExhaustedRetryPolicy,
) -> anyhow::Result<()> {
    // `try_persist_database` skips writing a database without changes, so
    // that isn't a persist for the metrics below.
    let has_changes = user_context.database.changed();
    let mut attempt: u64 = 1;
    let now = Instant::now();
    while attempt < MAX_RETRY_ATTEMPTS {
        match try_persist_database(user_context, metrics, policy).await? {
            MetadataPersistResult::Succeeded { committed_version } => {
                // Track our own write, so that the next sync doesn't mistake
                // it for a remote change. Without a version from the host,
                // keep the old one: the next sync then pulls our write back.
                if let Some(committed_version) = committed_version {
                    user_context.database_version = committed_version;
                }
                if has_changes {
                    // This includes any RESOURCE_EXHAUSTED backoff.
                    let elapsed = now.elapsed();
                    metrics.record_db_persist_latency_with_retries(elapsed.as_millis() as u64);
                    metrics.record_db_persist_attempts(attempt);
                }
                // Flush deferred blob soft-deletes now that the index is
                // durably persisted. Orphaned blobs are tracked in metrics
                // and can be cleaned by GC.
                let pending_count = user_context.database.meta_db().pending_blob_deletes().len();
                if let Err(e) = user_context.database.flush_pending_blob_deletes().await {
                    metrics.inc_orphaned_blob_deletes(pending_count as u64);
                    error!("{e}");
                }
                user_context.database.mark_persisted();
                return Ok(());
            }
            MetadataPersistResult::RetryNeeded => {
                attempt += 1;
                info!("Retrying db save (attempt {attempt})");
                pull_and_rebase(user_context, /* require_blob= */ true, metrics, policy).await?;
            }
        }
    }
    anyhow::bail!("Failed to persist after {} attempts", MAX_RETRY_ATTEMPTS);
}

/// Persists each session received on `rx` in its own task, with at most
/// `MAX_CONCURRENT_PERSISTS` persisting at once.
///
/// A session is only taken off `rx` when a worker slot is free, so sessions
/// waiting for a slot stay in `rx` and `rx.len()` is the number of queued
/// sessions.
///
/// Sessions are not ordered per `uid`. Sessions for the same `uid` may persist
/// concurrently: the versioned metadata write rejects a stale version, and
/// `persist_database` then rebases onto the latest blob and retries, as it
/// already must for writes from other enclaves and from `SyncDatabase`. As a
/// result, the mutations of the session whose write commits last are applied
/// last, regardless of the order in which the sessions closed.
pub async fn run_persistence_service(
    mut rx: mpsc::UnboundedReceiver<UserSessionContext>,
    metrics: Arc<Metrics>,
) {
    info!("Persistence service started");
    let mut persisting_tasks: JoinSet<()> = JoinSet::new();
    let mut rx_open = true;

    // Stay alive while:
    // 1. `rx_open`: the channel is open, even when idle (0 tasks in
    //    `persisting_tasks`).
    // 2. `!persisting_tasks.is_empty()`: save tasks are still running and must not
    //    be aborted.
    // Exits only when the channel closes AND all saves have drained.
    //
    // At least one branch is always enabled inside the loop: when all
    // `MAX_CONCURRENT_PERSISTS` slots are busy the `rx` branch is disabled, but
    // `persisting_tasks` is then non-empty.
    while rx_open || !persisting_tasks.is_empty() {
        tokio::select! {
            biased;
            maybe_ctx = rx.recv(),
                if rx_open && persisting_tasks.len() < MAX_CONCURRENT_PERSISTS =>
            {
                match maybe_ctx {
                    Some(user_context) => {
                        info!("Persistence service received a session to save");
                        metrics.record_db_persist_queue_size(rx.len() as u64);
                        persisting_tasks.spawn(persist_one_session(user_context, metrics.clone()));
                    }
                    None => {
                        rx_open = false;
                    }
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

#[cfg(test)]
mod tests {
    use std::{
        net::{IpAddr, Ipv4Addr, SocketAddr},
        sync::atomic::Ordering,
        time::SystemTime,
    };

    use oak_private_memory_database::{
        clock::{SystemClock, system_time_to_timestamp},
        database::{MAX_DATABASE_SIZE, MAX_GRPC_DECODE_SIZE},
    };
    use private_memory_test_database_server_lib::service::SealedMemoryDatabaseServiceTestImpl;
    use sealed_memory_rust_proto::prelude::v1::{
        AddMemoryRequest, KeySyncRequest, Memory, UserRegistrationRequest,
    };
    use tokio::net::TcpListener;
    use tonic::Code;

    use super::*;
    use crate::{
        MAX_MEMORY_TTL_SECONDS, METADATA_BLANKET_TTL_SECONDS, db_client::SharedDbClient,
        handler::SealedMemorySessionHandler,
    };

    type TestMetrics = metrics_testing::TestMetrics<Metrics>;

    /// A policy that retries quickly, so that tests don't wait for long.
    const FAST_RETRY_POLICY: ResourceExhaustedRetryPolicy = ResourceExhaustedRetryPolicy {
        initial_backoff: Duration::from_millis(2),
        max_backoff: Duration::from_millis(10),
        total_budget: Duration::from_secs(10),
    };

    fn test_metrics() -> TestMetrics {
        TestMetrics::new(Metrics::new)
    }

    fn resource_exhausted_retries(harness: &TestMetrics) -> u64 {
        harness.collect().counter("db_resource_exhausted_retries", &[])
    }

    /// Starts an in-process test database service backed by `service`.
    async fn start_test_db(service: Arc<SealedMemoryDatabaseServiceTestImpl>) -> SocketAddr {
        let listener =
            TcpListener::bind(SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), 0)).await.unwrap();
        let db_addr = listener.local_addr().unwrap();
        tokio::spawn(async move {
            let _ =
                private_memory_test_database_server_lib::service::serve(listener, service).await;
        });
        db_addr
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
        let (persistence_tx, _persistence_rx) = mpsc::unbounded_channel();
        let handler = SealedMemorySessionHandler::new(
            metrics.clone(),
            persistence_tx,
            Arc::new(SharedDbClient::new(db_addr, MAX_GRPC_DECODE_SIZE, metrics)),
            Arc::new(SystemClock),
            MAX_DATABASE_SIZE,
            METADATA_BLANKET_TTL_SECONDS,
            MAX_MEMORY_TTL_SECONDS,
            false,
            vec![],
        );
        let key_encryption_key = b"aaaabbbbccccddddeeeeffffgggghhhh".to_vec();
        handler
            .user_registration_handler(UserRegistrationRequest {
                pm_uid: pm_uid.to_string(),
                key_encryption_key: key_encryption_key.clone(),
                boot_strap_info: Some(Default::default()),
            })
            .await
            .unwrap();
        handler
            .key_sync_handler(KeySyncRequest {
                pm_uid: pm_uid.to_string(),
                key_encryption_key,
                session_config: None,
            })
            .await
            .unwrap();
        let memory = Memory {
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
            ..Default::default()
        };
        handler.add_memory_handler(AddMemoryRequest { memory: Some(memory) }).await.unwrap();
        let session = handler.session_context().await.take().unwrap();
        assert!(session.database.changed());
        session
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
            start_test_db(service.clone()).await,
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
            start_test_db(service.clone()).await,
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
            start_test_db(service.clone()).await,
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
            start_test_db(service.clone()).await,
            harness.metrics.clone(),
            pm_uid,
        )
        .await;
        let reads_before = service.metadata_read_calls.load(Ordering::SeqCst);
        let writes_before = service.metadata_write_calls.load(Ordering::SeqCst);
        service.fail_next_metadata_reads(Code::ResourceExhausted, 2).await;
        service.fail_next_metadata_writes(Code::ResourceExhausted, 2).await;

        sync_persist_database_with_policy(&mut session, &harness.metrics, FAST_RETRY_POLICY)
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
            start_test_db(service.clone()).await,
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
        sync_persist_database_with_policy(&mut session, &harness.metrics, one_retry_per_call)
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
            start_test_db(service.clone()).await,
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
}
