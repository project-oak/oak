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

use crate::systemd_journal::{Journal, JournalOpenFlags};
use anyhow::{Context, Result};
use oak_containers_orchestrator_client::LauncherClient;
use tokio::sync::mpsc;
use tokio_stream::wrappers::UnboundedReceiverStream;

pub async fn run(launcher_client: LauncherClient) -> Result<()> {
    // Journal is not Send, because the underlying systemd journal can't be shared between threads
    // (even with locking). Thus, let's wrap things in a channel.
    let (send, recv) = mpsc::unbounded_channel();

    let reader = async move {
        // Iterating over the journal can block (synchronously), so we need to wrap this in a
        // `spawn_blocking` call so that we don't hog the thread.
        let x = tokio::task::spawn_blocking(move || {
            let mut journal = Journal::new(JournalOpenFlags::ALL_NAMESPACES)?;
            journal.seek_head()?;

            // `(Journal as Iterator)::next()` will block if there is nothing to read
            for entry in journal {
                let entry = entry.context("failed to read next journal entry")?;
                // DEBUG will contain _tons_ of garbage; if you need that level of detail, you can
                // enable debug mode and log in directly.
                if entry
                    .get("PRIORITY")
                    .and_then(|val| val.parse::<i32>().ok())
                    .unwrap_or_default()
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
    let sender = async {
        launcher_client
            .log(UnboundedReceiverStream::new(recv))
            .await
            .map_err(|err| anyhow::anyhow!("error writing logs to launcher: {}", err))
    };
    tokio::try_join!(reader, sender).map(|((), ())| ())
}
