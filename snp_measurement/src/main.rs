//
// Copyright 2022 The Project Oak Authors
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

mod page;
mod stage0;
mod vmsa;

use crate::{
    stage0::load_stage0,
    vmsa::{get_boot_vmsa, VMSA_ADDRESS},
};
use clap::Parser;
use page::PageInfo;
use std::path::PathBuf;

/// The default workspace-relative path to the Stage 0 firmware ROM image.
const DEFAULT_STAGE0_ROM: &str = "stage0/target/x86_64-unknown-none/release/stage0.bin";

#[derive(Parser, Clone)]
#[command(about = "Oak SEV-SNP Measurement Calculator")]
struct Cli {
    #[arg(long, help = "The location of the Stage 0 firmware ROM image")]
    stage0_rom: Option<PathBuf>,
}

impl Cli {
    fn stage0_path(&self) -> PathBuf {
        self.stage0_rom
            .clone()
            .unwrap_or_else(|| format!("{}/{}", env!("WORKSPACE_ROOT"), DEFAULT_STAGE0_ROM).into())
    }
}

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let cli = Cli::parse();

    let stage0 = load_stage0(cli.stage0_path())?;

    let mut page_info = PageInfo::new();
    // Add the Stage 0 firmware ROM image.
    page_info.update_from_data(stage0.rom_bytes(), stage0.start_address);
    // Add the legacy boot shadow of the Stage 0 firmware ROM image.
    page_info.update_from_data(stage0.legacy_shadow_bytes(), stage0.legacy_start_address);

    // TODO(#3486): Also include the enclave binary and SNP-specific pages.

    // For now we assume there will only be one vCPU in the VM.
    page_info.update_from_vmsa(&get_boot_vmsa(), VMSA_ADDRESS);

    println!(
        "Attestation Measurement: {}",
        hex::encode(page_info.digest_cur)
    );
    Ok(())
}
