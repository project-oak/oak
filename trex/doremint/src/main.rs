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

#![feature(try_blocks)]

mod blob;
mod flags;
mod image;
mod repository;

use clap::{Parser, Subcommand};
use oci_spec::distribution::Reference;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Commands,

    #[arg(
        long,
        global = true,
        help = "Path to write the output to. Use '-' for stdout.",
        default_value = ""
    )]
    output: Option<flags::Output>,

    #[arg(long, global = true, help = "An OCI Image reference")]
    pub image: Option<Reference>,
}

impl Args {
    async fn run(&mut self) -> anyhow::Result<()> {
        self.command.run().await
    }
}

#[derive(Subcommand, Debug)]
enum Commands {
    Image(image::Image),
    Blob(blob::Blob),
}

impl Commands {
    async fn run(&self) -> anyhow::Result<()> {
        match self {
            Self::Image(args) => args.run().await,
            Self::Blob(args) => args.run().await,
        }
    }
}

#[tokio::main]
async fn main() {
    env_logger::init();
    let mut args = Args::parse();

    let result = args.run();

    if let Err(err) = result.await {
        eprintln!("Error: {err:?}");
        std::process::exit(1);
    }
}
