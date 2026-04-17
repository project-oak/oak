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

use std::path::PathBuf;

use anyhow::Context;
use goblin::elf::{Elf, program_header::PT_LOAD};
use log::{debug, info};
use sha2::{Digest, Sha256};
use x86_64::PhysAddr;

/// A memory segment extracted from an ELF file.
pub struct MemorySegment {
    /// The guest-physical start address of the segment.
    pub start_address: PhysAddr,
    /// The data specified for the segment in the ELF file.
    pub data: Vec<u8>,
}

/// Loads an ELF file and extracts the non-zero loadable memory segments.
pub fn load_elf_segments(elf_path: PathBuf) -> anyhow::Result<Vec<MemorySegment>> {
    let elf_bytes = load_elf_file(elf_path)?;
    let elf = Elf::parse(&elf_bytes).context("invalid ELF file")?;
    // For now we assume each segment's start address will be 4KiB aligned, so we do
    // not pad the start. This assumption is validated when the segments are
    // measured.
    Ok(elf
        .program_headers
        .iter()
        .filter(|header| header.p_type == PT_LOAD && header.p_filesz > 0)
        .map(|header| MemorySegment {
            start_address: PhysAddr::new(header.p_paddr),
            data: elf_bytes[header.file_range()].to_vec(),
        })
        .collect())
}

fn load_elf_file(elf_path: PathBuf) -> anyhow::Result<Vec<u8>> {
    let elf_bytes = std::fs::read(elf_path).context("couldn't load ELF file")?;
    debug!("ELF file size: {}", elf_bytes.len());
    let mut elf_hasher = Sha256::new();
    elf_hasher.update(&elf_bytes);
    let elf_sha256_digest = elf_hasher.finalize();
    info!("ELF file digest: sha256:{}", hex::encode(elf_sha256_digest));
    Ok(elf_bytes)
}
