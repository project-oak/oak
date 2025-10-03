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

//! Endorscope tool: lists and verifies endorsements on static storage.

use clap::{Parser, Subcommand};
use oak_time::Instant;
use oak_time_std::instant::now;

mod list;
mod verify;

#[derive(Parser)]
struct Params {
    #[arg(long, help = "Time in milliseconds UTC since Unix Epoch or current time if not set.")]
    now_utc_millis: Option<i64>,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    #[command(subcommand = "verify", about = "Verify an endorsement.")]
    Verify {
        #[command(subcommand)]
        command: verify::VerifyCommands,
    },

    #[command(subcommand = "list", about = "List endorsements.")]
    List(list::ListArgs),
}

fn main() {
    let p = Params::parse();
    let current_time = p.now_utc_millis.map(Instant::from_unix_millis).unwrap_or_else(now);

    match p.command {
        Commands::Verify { command } => match command {
            verify::VerifyCommands::File(args) => verify::verify_file(current_time, args),
            verify::VerifyCommands::Remote(args) => verify::verify_remote(current_time, args),
        },
        Commands::List(args) => list::list(current_time, args),
    }
}
