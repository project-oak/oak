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

use std::collections::HashMap;

use anyhow::Result;
use oak_containers_orchestrator_client::LauncherClient;
use systemd::journal;

pub async fn run(launcher_client: LauncherClient) -> Result<()> {
    let mut journal = journal::OpenOptions::default()
        .all_namespaces(true)
        .open()?;
    journal.seek_head()?;

    loop {
        // Read all entries we can.
        let mut entries = Vec::new();
        while let Some(entry) = journal.next_entry()? {
            // DEBUG will contain _tons_ of garbage; if you need that level of detail, you can
            // enable debug mode and log in directly. If
            if entry
                .get("PRIORITY")
                .map(String::as_str)
                .unwrap_or_default()
                .parse()
                .map(|prio: i32| prio > 6)
                .unwrap_or_default()
            {
                continue;
            }

            // Newer versions of tokio can be
            // configured to use BTreeMap directly, but we can't switch to that version
            // due to dependencies being a mess
            entries.push({
                let mut fields = HashMap::new();
                fields.extend(entry);
                fields
            });
        }

        launcher_client
            .log(entries)
            .await
            .map_err(|err| anyhow::anyhow!("failed to send log entries: {}", err))?;

        // Out of data to read. Wait for something to appear.
        journal.wait(None)?;
    }
}
