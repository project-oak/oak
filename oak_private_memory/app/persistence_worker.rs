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

use anyhow::Context;
use external_db_client::{DataBlobHandler, MetadataPersistResult};
use log::{error, info, warn};
use metrics::Metrics;
use oak_private_memory_database::encryption::{decrypt_database, encrypt_database};
use prost::Message;
use sealed_memory_rust_proto::{
    oak::private_memory::EncryptedMetadataBlob, prelude::v1::SyncDatabaseResponse,
};
use tokio::{sync::mpsc, task::JoinSet, time::Instant};

static MAX_RETRY_ATTEMPTS: u64 = 25;

/// Maximum number of user sessions persisted concurrently by the background
/// persistence worker.
pub(crate) const MAX_CONCURRENT_PERSISTS: usize = 8;

/// Minimum number of optimizable (deleted/expired) documents before calling
/// Icing.Optimize. GetOptimizeInfo (~0.16ms) is called on every persist to
/// check, and Optimize (~1s) is only called when this threshold is exceeded.
pub(crate) const OPTIMIZE_DOC_THRESHOLD: i64 = 100;

use crate::context::UserSessionContext;

// Attempt to persist the database once.
// If there is a failure due to a version mismatch,
// Ok(MetadataPersisteResult::RetryNeeded) will be returned. The caller should
// re-fetch the latest metadatablob and rebase the icing database and try again.
async fn try_persist_database(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
) -> anyhow::Result<MetadataPersistResult> {
    if !user_context.database.changed() {
        info!("Database is not changed, skip saving");
        return Ok(MetadataPersistResult::Succeeded);
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

    let now = Instant::now();
    let coarsened_expiration_timestamp = user_context.database.calculate_coarsened_blanket_ttl();
    let result = user_context
        .database_service_client
        .add_metadata_blob_stream(
            &user_context.uid,
            EncryptedMetadataBlob {
                encrypted_data_blob: Some(database),
                version: user_context.database_version.clone(),
            },
            coarsened_expiration_timestamp,
        )
        .await?;

    if result == MetadataPersistResult::Succeeded {
        let elapsed = now.elapsed();
        metrics.record_db_persist_latency(elapsed.as_millis() as u64);
        metrics.record_db_size(db_size as u64);
        metrics.record_db_save_speed(metrics::transfer_speed_kb_per_ms(encoded_size, elapsed));
    }

    Ok(result)
}

/// Fetch the latest remote blob and rebase the local database onto it.
///
/// If `require_blob` is true, a missing blob is an error (used on CAS retry).
/// If false, a missing blob is silently skipped (used for initial sync where
/// the user may not have any persisted data yet).
async fn pull_and_rebase(
    user_context: &mut UserSessionContext,
    require_blob: bool,
    metrics: &Metrics,
) -> anyhow::Result<()> {
    let coarsened_expiration_timestamp = user_context.database.calculate_coarsened_blanket_ttl();
    let fetch_start = Instant::now();
    let refreshed_blob = user_context
        .database_service_client
        .get_metadata_blob_stream(&user_context.uid, coarsened_expiration_timestamp)
        .await?;
    let fetch_elapsed = fetch_start.elapsed();

    let refreshed_blob = match refreshed_blob {
        Some(blob) => blob,
        None if require_blob => anyhow::bail!("no blob found"),
        None => return Ok(()),
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
pub async fn sync_persist_database(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
) -> anyhow::Result<SyncDatabaseResponse> {
    // Pull: fetch the latest remote blob and rebase so that remote changes
    // become visible in this session's local database.
    pull_and_rebase(user_context, /* require_blob= */ false, metrics).await?;

    // Optimize is expensive (~1s for a 30MB database) and always rebuilds
    // the entire index. Use GetOptimizeInfo (~0.16ms) to check whether
    // there are enough deleted/expired documents to warrant optimization.
    maybe_optimize(&mut user_context.database, metrics)?;

    // Push: persist any local changes (now rebased on top of the latest remote
    // state).
    persist_database(user_context, metrics).await?;

    Ok(SyncDatabaseResponse {})
}

async fn persist_one_session(mut user_context: UserSessionContext, metrics: Arc<Metrics>) {
    // Optimize is expensive (~1s for a 30MB database) and always rebuilds
    // the entire index. Use GetOptimizeInfo (~0.16ms) to check whether
    // there are enough deleted/expired documents to warrant optimization.
    if let Err(e) = maybe_optimize(&mut user_context.database, &metrics) {
        error!("optimizing database: {e:?}");
    }

    if let Err(e) = persist_database(&mut user_context, &metrics).await {
        metrics.inc_db_persist_failures();
        error!("Failed to persist database: {:?}", e);
    }
}

// Attempt to persist the database up to MAX_RETRY_ATTEMPTS times.
// Retries only occur when the FailedPrecondition error code is returned from
// the underlying database layer.
async fn persist_database(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
) -> anyhow::Result<()> {
    // `try_persist_database` skips writing a database without changes, so
    // that isn't a persist for the metrics below.
    let has_changes = user_context.database.changed();
    let mut attempt: u64 = 1;
    let now = Instant::now();
    while attempt < MAX_RETRY_ATTEMPTS {
        match try_persist_database(user_context, metrics).await {
            Ok(MetadataPersistResult::Succeeded) => {
                if has_changes {
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
            Ok(MetadataPersistResult::RetryNeeded) => {
                attempt += 1;
                info!("Retrying db save (attempt {attempt})");
                pull_and_rebase(user_context, /* require_blob= */ true, metrics).await?;
            }
            Err(e) => return Err(e),
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
