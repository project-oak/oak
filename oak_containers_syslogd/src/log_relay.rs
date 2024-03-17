//
// Copyright 2023 The Project Oak Authors
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
    sync::Arc,
    time::{Duration, SystemTime},
};

use anyhow::{Context, Result};
use oak_containers_orchestrator::launcher_client::LauncherClient;
use opentelemetry::logs::{AnyValue, LogRecord, Logger, Severity};
use tokio::sync::{mpsc, OnceCell};

use crate::systemd_journal::{Journal, JournalOpenFlags};

pub async fn run(launcher_client: LauncherClient, terminate: Arc<OnceCell<()>>) -> Result<()> {
    // Journal is not Send, because the underlying systemd journal can't be shared
    // between threads (even with locking). Thus, let's wrap things in a
    // channel.
    let (send, mut recv) = mpsc::unbounded_channel();

    let reader = async move {
        // Iterating over the journal can block (synchronously), so we need to wrap this
        // in a `spawn_blocking` call so that we don't hog the thread.
        let x = tokio::task::spawn_blocking(move || {
            let mut journal = Journal::new(JournalOpenFlags::ALL_NAMESPACES, terminate)?;
            journal.seek_head()?;

            // `(Journal as Iterator)::next()` will block if there is nothing to read
            for entry in journal {
                let entry = entry.context("failed to read next journal entry")?;
                // DEBUG will contain _tons_ of garbage; if you need that level of detail, you
                // can enable debug mode and log in directly.
                if entry.get("PRIORITY").and_then(|val| val.parse::<i32>().ok()).unwrap_or_default()
                    > 6
                {
                    continue;
                }
                send.send(entry)?;
            }

            Ok(())
        });
        x.await?
    };
    let logger = opentelemetry_otlp::new_pipeline()
        .logging()
        .with_exporter(launcher_client.openmetrics_builder())
        .install_batch(opentelemetry_sdk::runtime::Tokio)
        .context("could not create OTLP logger")?;
    let sender = async {
        while let Some(mut msg) = recv.recv().await {
            let mut builder = LogRecord::builder();
            // PRIORITY
            if let Some(val) = msg.remove("PRIORITY") {
                builder = builder.with_severity_number(match val.parse()? {
                    // EMERGENCY
                    0 => Severity::Error4,
                    // ALERT
                    1 => Severity::Error3,
                    // CRITICAL
                    2 => Severity::Error2,
                    // ERROR
                    3 => Severity::Error,
                    // WARNING
                    4 => Severity::Warn,
                    // NOTICE
                    5 => Severity::Info2,
                    // INFORMATIONAL
                    6 => Severity::Info,
                    // DEBUG
                    7 => Severity::Debug,
                    // lower priorities
                    _ => Severity::Trace,
                });
            }
            if let Some(val) = msg.remove("_SOURCE_REALTIME_TIMESTAMP") {
                builder = builder
                    .with_timestamp(SystemTime::UNIX_EPOCH + Duration::from_secs(val.parse()?));
            }
            if let Some(val) = msg.remove("MESSAGE") {
                builder = builder.with_body(AnyValue::String(val.into()));
            }
            builder = builder.with_attributes(
                msg.into_iter().map(|(k, v)| (k.into(), AnyValue::String(v.into()))).collect(),
            );
            logger.emit(builder.build());
        }
        Ok(())
    };

    tokio::try_join!(reader, sender).map(|((), ())| ())
}
