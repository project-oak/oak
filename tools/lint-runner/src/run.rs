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

use std::{process::Stdio, sync::Arc, time::Instant};

use anyhow::{Context, Result};
use futures::StreamExt;
use tokio::{process::Command, sync::Semaphore};

use crate::{config::Tool, identify::FileWithTags, ui::Dashboard};

/// The result of running a single tool.
pub struct ToolResult {
    /// The display name of the tool.
    pub name: String,
    /// Whether the tool execution was successful.
    pub success: bool,
    /// The combined stdout and stderr output of the tool.
    pub output: String,
}

/// The internal outcome of a single command execution.
struct CmdOutcome {
    /// Whether the command execution was successful.
    success: bool,
    /// The combined stdout and stderr output of the command.
    output: String,
}

/// Runs a single command with a list of files, respecting the given semaphore
/// for concurrency control.
async fn run_cmd(entry: String, files: Vec<String>, sem: Arc<Semaphore>) -> Result<CmdOutcome> {
    let _permit = sem.acquire().await?;
    let parts = shlex::split(&entry).context("shlex split failed")?;
    if parts.is_empty() {
        return Ok(CmdOutcome { success: true, output: "".into() });
    }

    let out = Command::new(&parts[0])
        .args(&parts[1..])
        .args(files)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?
        .wait_with_output()
        .await?;

    Ok(CmdOutcome {
        success: out.status.success(),
        output: format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        ),
    })
}

/// Orchestrates the execution of multiple tools over a set of files.
///
/// This function manages concurrency, batching of files, and updates the
/// dashboard UI.
pub async fn run_tool_session(
    active: Vec<Tool>,
    file_tags: Vec<FileWithTags>,
    jobs: Option<usize>,
    batch_size: usize,
) -> Result<Vec<ToolResult>> {
    let global_sem = Arc::new(Semaphore::new(jobs.unwrap_or(num_cpus::get())));
    let file_tags = Arc::new(file_tags);

    // Initialize Dashboard UI
    let dashboard = Arc::new(Dashboard::new(&active, &file_tags));

    let results = futures::stream::iter(active.into_iter().enumerate())
        .map(|(idx, t)| {
            let name = t.display_name().to_string();
            let matched: Vec<String> = file_tags
                .iter()
                .filter(|f| t.matches(&f.path, &f.tags))
                .map(|f| f.path.clone())
                .collect();
            let (t_entry, sem, db) = (t.entry.clone(), global_sem.clone(), dashboard.clone());

            async move {
                let start = Instant::now();
                let chunks: Vec<Vec<String>> =
                    matched.chunks(batch_size).map(|c| c.to_vec()).collect();
                let mut chunk_stream = futures::stream::iter(chunks)
                    .map(|c| run_cmd(t_entry.clone(), c, sem.clone()))
                    .buffer_unordered(100);

                let (mut success, mut out) = (true, String::new());
                while let Some(res) = chunk_stream.next().await {
                    let outcome = res?;
                    if !outcome.success {
                        success = false;
                    }
                    out.push_str(&outcome.output);
                }

                let dur = start.elapsed();
                db.update(idx, &name, success, matched.len(), dur)?;
                Ok::<ToolResult, anyhow::Error>(ToolResult { name, success, output: out })
            }
        })
        .buffer_unordered(dashboard.num_active())
        .collect::<Vec<_>>()
        .await;

    results.into_iter().collect()
}
