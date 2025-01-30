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

mod measure;
use std::path::PathBuf;

use clap::Parser;
use hex::ToHex;

#[derive(Parser, Clone, Debug)]
#[command(about = "Oak Tdx Measurement Calculator")]
struct Cli {
    #[arg(long, help = "The location of the Stage 0 firmware ROM image")]
    stage0_rom: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    let stage0_bin: Vec<u8> = std::fs::read(cli.stage0_rom).unwrap();
    println!("{}", measure::mr_td_measurement(&stage0_bin).encode_hex::<String>());

    Ok(())
}
