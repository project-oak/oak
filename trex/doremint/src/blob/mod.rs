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

pub mod endorse;

use clap::{Parser, Subcommand};

#[derive(Parser, Debug)]
#[command(about = "Work with blobs")]
pub struct Blob {
    #[command(subcommand)]
    pub command: BlobCommands,
}

impl Blob {
    pub async fn run(&self) -> anyhow::Result<()> {
        self.command.run().await
    }
}

#[derive(Subcommand, Debug)]
pub enum BlobCommands {
    Endorse(endorse::Endorse),
}

impl BlobCommands {
    pub async fn run(&self) -> anyhow::Result<()> {
        match self {
            Self::Endorse(cmd) => cmd.run().await,
        }
    }
}
