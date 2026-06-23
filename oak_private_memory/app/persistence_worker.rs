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
use anyhow::Context;
use external_db_client::{DataBlobHandler, MetadataPersistResult};
use log::{error, info};
use metrics::get_global_metrics;
use oak_private_memory_database::encryption::{decrypt_database, encrypt_database};
use prost::Message;
use sealed_memory_rust_proto::{
    oak::private_memory::EncryptedMetadataBlob, prelude::v1::SyncDatabaseResponse,
};
use tokio::{sync::mpsc, time::Instant};

static MAX_RETRY_ATTEMPTS: u64 = 25;

/// Minimum number of optimizable (deleted/expired) documents before calling
/// Icing.Optimize. GetOptimizeInfo (~0.16ms) is called on every persist to
/// check, and Optimize (~1s) is only called when this threshold is exceeded.
static OPTIMIZE_DOC_THRESHOLD: i64 = 100;

use crate::context::UserSessionContext;

// Attempt to persist the database once.
// If there is a failure due to a version mismatch,
// Ok(MetadataPersisteResult::RetryNeeded) will be returned. The caller should
// re-fetch the latest metadatablob and rebase the icing database and try again.
async fn try_persist_database(
    user_context: &mut UserSessionContext,
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
        // Database exceeds the maximum allowed size.
        info!("Database is too large to save: {} (limit: {})", db_size, max_database_size);
        anyhow::bail!("Database is too large to save: {} (limit: {})", db_size, max_database_size);
    }
    info!("Saving db size: {}", db_size);
    get_global_metrics().record_db_size(db_size as u64);

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
        get_global_metrics().record_db_persist_latency(elapsed.as_millis() as u64);
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
) -> anyhow::Result<()> {
    let coarsened_expiration_timestamp = user_context.database.calculate_coarsened_blanket_ttl();
    let refreshed_blob = user_context
        .database_service_client
        .get_metadata_blob_stream(&user_context.uid, coarsened_expiration_timestamp)
        .await?;

    let refreshed_blob = match refreshed_blob {
        Some(blob) => blob,
        None if require_blob => anyhow::bail!("no blob found"),
        None => return Ok(()),
    };

    if refreshed_blob.version == user_context.database_version {
        return Ok(());
    }

    let encrypted_data_blob =
        refreshed_blob.encrypted_data_blob.context("missing encrypted data blob")?;
    let decrypted = decrypt_database(encrypted_data_blob, &user_context.dek)?;
    let new_icing_db = decrypted.icing_db.context("missing icing_db in refreshed blob")?;
    let failed_operations =
        user_context.database.rebase(new_icing_db.encode_to_vec().as_slice())?;
    if failed_operations > 0 {
        get_global_metrics().inc_db_rebase_operation_failures(failed_operations as u64);
    }
    user_context.database_version = refreshed_blob.version;
    Ok(())
}

/// Synchronously persist the database.
///
/// This is the public API for the SyncDatabase RPC handler. It pulls the latest
/// remote state (which may include writes from other sessions), rebases the
/// local database, then pushes any local changes.
pub async fn sync_persist_database(
    user_context: &mut UserSessionContext,
) -> anyhow::Result<SyncDatabaseResponse> {
    // Pull: fetch the latest remote blob and rebase so that remote changes
    // become visible in this session's local database.
    pull_and_rebase(user_context, /* require_blob= */ false).await?;

    // Push: persist any local changes (now rebased on top of the latest remote
    // state).
    persist_database(user_context).await?;

    Ok(SyncDatabaseResponse {})
}

// Attempt to persist the database up to MAX_RETRY_ATTEMPTS times.
// Retries only occur when the FailedPrecondition error code is returned from
// the underlying database layer.
async fn persist_database(user_context: &mut UserSessionContext) -> anyhow::Result<()> {
    let mut attempt: u64 = 1;
    let now = Instant::now();
    while attempt < MAX_RETRY_ATTEMPTS {
        match try_persist_database(user_context).await {
            Ok(MetadataPersistResult::Succeeded) => {
                let elapsed = now.elapsed();
                get_global_metrics()
                    .record_db_persist_latency_with_retries(elapsed.as_millis() as u64);
                get_global_metrics().record_db_persist_attempts(attempt);
                // Flush deferred blob soft-deletes now that the index is
                // durably persisted. Orphaned blobs are tracked in metrics
                // and can be cleaned by GC.
                let pending_count = user_context.database.meta_db().pending_blob_deletes().len();
                if let Err(e) = user_context.database.flush_pending_blob_deletes().await {
                    get_global_metrics().inc_orphaned_blob_deletes(pending_count as u64);
                    error!("{e}");
                }
                user_context.database.mark_persisted();
                return Ok(());
            }
            Ok(MetadataPersistResult::RetryNeeded) => {
                attempt += 1;
                info!("Retrying db save (attempt {attempt})");
                pull_and_rebase(user_context, /* require_blob= */ true).await?;
            }
            Err(e) => return Err(e),
        }
    }
    anyhow::bail!("Failed to persist after {} attempts", MAX_RETRY_ATTEMPTS);
}

pub async fn run_persistence_service(mut rx: mpsc::UnboundedReceiver<UserSessionContext>) {
    info!("Persistence service started");
    while let Some(mut user_context) = rx.recv().await {
        info!("Persistence service received a session to save");
        get_global_metrics().record_db_persist_queue_size(rx.len() as u64);

        // Optimize is expensive (~1s for a 30MB database) and always rebuilds
        // the entire index. Use GetOptimizeInfo (~0.16ms) to check whether
        // there are enough deleted/expired documents to warrant optimization.
        match user_context.database.get_optimize_info() {
            Ok(info) if info.optimizable_docs() > OPTIMIZE_DOC_THRESHOLD => {
                info!("optimizing database ({} optimizable docs)", info.optimizable_docs());
                let now = Instant::now();
                if let Err(e) = user_context.database.optimize() {
                    error!("optimizing database: {e:?}");
                } else {
                    let elapsed = now.elapsed();
                    get_global_metrics().record_db_optimize_latency(elapsed.as_millis() as u64);
                }
            }
            Err(e) => {
                error!("getting optimize info: {e:?}");
            }
            _ => {}
        }

        if let Err(e) = persist_database(&mut user_context).await {
            get_global_metrics().inc_db_persist_failures();
            info!("Failed to persist database: {:?}", e);
        }
    }
    info!("Persistence service finished");
}
