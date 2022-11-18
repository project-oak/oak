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

use anyhow::Context;
use log::{debug, info};
use sha2::{Digest, Sha256};
use std::path::PathBuf;
use x86_64::PhysAddr;

/// The address of the first byte after the end of the firmware image.
///
/// The firmware image gets loaded just below the 4GiB boundary.
pub const FIRMWARE_TOP: PhysAddr = PhysAddr::new(0x1_0000_0000);

/// Loads the Stage0 firmware ROM image from the supplied path.
pub fn load_stage0(stage0_rom_path: PathBuf) -> anyhow::Result<Vec<u8>> {
    let stage0_bytes =
        std::fs::read(&stage0_rom_path).context("couldn't load stage0 firmware ROM image")?;
    debug!("Stage0 size: {}", stage0_bytes.len());

    let mut stage0_hasher = Sha256::new();
    stage0_hasher.update(&stage0_bytes);
    let stage0_cecksum = stage0_hasher.finalize();
    info!("Stage0 SHA256 hash: {}", hex::encode(stage0_cecksum));
    Ok(stage0_bytes)
}
