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
const FIRMWARE_TOP: PhysAddr = PhysAddr::new(0x1_0000_0000);

/// The address of the first byte after the end of the legacy boot shadow firmware image.
///
/// To support legacy booting the last 128KiB of the firmware gets shadowed just below the end of
/// 20-bit memory.
const LEGACY_TOP: PhysAddr = PhysAddr::new(0x10_0000);

/// The maximum size of the shadow firmware for legacy boot.
const LEGACY_MAX_SIZE: usize = 128 * 1024;

/// The contents of the Stage 0 firmware ROM image and its associated metadata.
pub struct Stage0Info {
    /// The bytes of the State 0 firmware ROM image.
    bytes: Vec<u8>,
    /// The start address of the firmware ROM in guest memory.
    pub start_address: PhysAddr,
    /// The start address of the legacy boot shadow of the firmware ROM in guest memory.
    pub legacy_start_address: PhysAddr,
    /// The offset into the firmware ROM image from where the legacy boot shadow starts.
    legacy_offset: usize,
}

impl Stage0Info {
    /// Gets the bytes of the entire ROM image.
    pub fn rom_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    /// Gets the bytes of the legacy boot shadow of the ROM image.
    pub fn legacy_shadow_bytes(&self) -> &[u8] {
        &self.bytes[self.legacy_offset..]
    }

    fn new(bytes: Vec<u8>) -> Self {
        let size = bytes.len();
        let start_address = FIRMWARE_TOP - size;
        let legacy_size = size.min(LEGACY_MAX_SIZE);
        let legacy_start_address = LEGACY_TOP - legacy_size;
        let legacy_offset = size - legacy_size;
        Self {
            bytes,
            start_address,
            legacy_start_address,
            legacy_offset,
        }
    }
}

/// Loads the Stage 0 firmware ROM image from the supplied path.
pub fn load_stage0(stage0_rom_path: PathBuf) -> anyhow::Result<Stage0Info> {
    let stage0_bytes =
        std::fs::read(&stage0_rom_path).context("couldn't load stage0 firmware ROM image")?;
    debug!("Stage0 size: {}", stage0_bytes.len());

    let mut stage0_hasher = Sha256::new();
    stage0_hasher.update(&stage0_bytes);
    let stage0_sha256_digest = stage0_hasher.finalize();
    info!(
        "Stage0 digest: sha256:{}",
        hex::encode(stage0_sha256_digest)
    );
    Ok(Stage0Info::new(stage0_bytes))
}
