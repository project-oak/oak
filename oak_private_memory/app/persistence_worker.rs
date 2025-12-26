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
use log::info;
use metrics::get_global_metrics;
use oak_private_memory_database::encryption::{decrypt_database, encrypt_database};
use prost::Message;
use sealed_memory_rust_proto::oak::private_memory::EncryptedMetadataBlob;
use tokio::{sync::mpsc, time::Instant};

static MAX_RETRY_ATTEMPTS: u64 = 25;

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
    let encrypted_info = exported_db.encrypted_info.context("Encrypted info is empty")?;
    let database = encrypt_database(&encrypted_info, &user_context.dek)?;

    let db_size = database.data.len() as u64;
    info!("Saving db size: {}", db_size);
    get_global_metrics().record_db_size(db_size);

    let now = Instant::now();
    let result = user_context
        .database_service_client
        .add_metadata_blob(
            &user_context.uid,
            EncryptedMetadataBlob {
                encrypted_data_blob: Some(database),
                version: user_context.database_version.clone(),
            },
        )
        .await?;

    if result == MetadataPersistResult::Succeeded {
        let elapsed = now.elapsed();
        get_global_metrics().record_db_persist_latency(elapsed.as_millis() as u64);
    }

    Ok(result)
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
                return Ok(());
            }
            Ok(MetadataPersistResult::RetryNeeded) => {
                attempt += 1;
                info!("Retrying db save (attempt {attempt}");
                // rebase the database and try again
                let refreshed_blob = user_context
                    .database_service_client
                    .get_metadata_blob(&user_context.uid)
                    .await?
                    .context("no blob found")?;

                let encrypted_data_blob =
                    refreshed_blob.encrypted_data_blob.context("missing encrypted data blob")?;

                let new_icing_db = decrypt_database(encrypted_data_blob, &user_context.dek)?
                    .icing_db
                    .context("missing icing_db in refreshed blob result")?;

                user_context.database.rebase(new_icing_db.encode_to_vec().as_slice())?;
                user_context.database_version = refreshed_blob.version;
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
        if let Err(e) = persist_database(&mut user_context).await {
            get_global_metrics().inc_db_persist_failures();
            info!("Failed to persist database: {:?}", e);
        }
    }
    info!("Persistence service finished");
}
