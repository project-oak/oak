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

mod flags;
mod image;

use std::io::Write;

use clap::{Parser, Subcommand};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Commands,
    #[arg(
        long,
        global = true,
        help = "Path to write the output to. Use '-' for stdout.",
        default_value = "-"
    )]
    output: flags::Output,
}

impl Args {
    fn run(&mut self, writer: &mut dyn Write) -> anyhow::Result<()> {
        self.command.run(writer)
    }
}

#[derive(Subcommand, Debug)]
enum Commands {
    Image(image::Image),
}

impl Commands {
    fn run(&self, writer: &mut dyn Write) -> anyhow::Result<()> {
        match self {
            Self::Image(args) => args.run(writer),
        }
    }
}

fn main() {
    let mut args = Args::parse();
    let result = (|| {
        let mut writer = args.output.open()?;
        args.run(&mut writer)
    })();

    if let Err(err) = result {
        eprintln!("Error: {err:?}");
        std::process::exit(1);
    }
}
