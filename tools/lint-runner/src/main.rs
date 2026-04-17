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

use std::{
    io::{self, IsTerminal, Read},
    time::Instant,
};

use anyhow::Result;
use clap::Parser;
use colored::*;
use oak_lint_runner::{
    config::{Config, select_active_tools},
    identify::identify_files_parallel,
    run::run_tool_session,
    ui::{print_skipped, report_summary},
};

/// Command line arguments for the oak_lint_runner.
#[derive(Parser, Debug)]
struct Args {
    /// List of files to run the linting tools on.
    files: Vec<String>,
    /// Path to the configuration file.
    #[arg(long, default_value = ".oak-lint-config.toml")]
    config: String,
    /// Maximum number of concurrent jobs.
    #[arg(short, long)]
    jobs: Option<usize>,
    /// Number of files to process in a single tool execution batch.
    #[arg(short, long, default_value_t = 50)]
    batch_size: usize,
    /// Optional ID of a single tool to run.
    #[arg(short, long)]
    tool: Option<String>,
}

/// Retrieves the list of files to be processed, either from command line
/// arguments or from stdin.
fn get_files(args: &Args) -> Result<Vec<String>> {
    let mut files = args.files.clone();
    if files.is_empty() && !io::stdin().is_terminal() {
        let mut buf = String::new();
        io::stdin().read_to_string(&mut buf)?;
        files = buf.lines().map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect();
    }
    if files.is_empty() {
        println!("{}", "No files provided.".red());
    }
    Ok(files)
}

/// The main entry point for the oak_lint_runner.
#[tokio::main]
async fn main() -> Result<()> {
    let args = Args::parse();
    let mut files = get_files(&args)?;
    if files.is_empty() {
        return Ok(());
    }

    let config: Config = toml::from_str(&std::fs::read_to_string(&args.config)?)?;

    // Apply global exclude immediately to optimize subsequent phases
    if let Some(global_ex) = config.get_global_exclude() {
        files.retain(|f| !global_ex.is_match(f));
    }

    if files.is_empty() {
        println!("{}", "No files remaining after global exclude filter.".blue());
        return Ok(());
    }

    let file_tags = identify_files_parallel(&files).await?;
    let selection = select_active_tools(&config, &file_tags);
    let (mut active, mut skipped) = (selection.active, selection.skipped);

    if let Some(tool_id) = &args.tool {
        active.retain(|t| t.id == *tool_id);
        skipped.retain(|t| t.id == *tool_id);
        if active.is_empty() && skipped.is_empty() {
            println!("{}", format!("Tool with ID '{}' not found in config.", tool_id).red());
            return Ok(());
        }
    }

    print_skipped(&skipped);
    if active.is_empty() {
        println!("{}", "No active tools for the provided files.".blue());
        return Ok(());
    }

    let start_total = Instant::now();
    let results = run_tool_session(active, file_tags, args.jobs, args.batch_size).await?;

    report_summary(&results, start_total.elapsed());

    if results.iter().any(|r| !r.success) {
        anyhow::bail!("one or more tools failed");
    }
    Ok(())
}
