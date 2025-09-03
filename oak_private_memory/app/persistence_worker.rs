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
use external_db_client::DataBlobHandler;
use log::info;
use metrics::get_global_metrics;
use oak_private_memory_database::encryption::encrypt_database;
use tokio::{sync::mpsc, time::Instant};

use crate::context::UserSessionContext;
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
