//
// Copyright 2023 The Project Oak Authors
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

use crate::try_parse_phys_addr;
use anyhow::Context;
use oak_dice::evidence::{Stage0DiceData, STAGE0_MAGIC};
use std::{
    fs::{read_dir, read_to_string, OpenOptions},
    io::{Read, Seek},
};
use x86_64::PhysAddr;
use zerocopy::{AsBytes, FromZeroes};

#[derive(Debug)]
struct MemoryRange {
    start: PhysAddr,
    end: PhysAddr,
    type_description: String,
}

/// The expected string representation of the custom type for the reserved memory range that
/// contains the DICE data.
///
/// Since we use a custom type the Linux Kernel does not recognize it. The text is defined in
/// <https://github.com/torvalds/linux/blob/d88520ad73b79e71e3ddf08de335b8520ae41c5c/arch/x86/kernel/e820.c#L1086>.
const EXPECTED_E820_TYPE: &str = "Unknown E820 type";

/// The path for reading the memory map from the sysfs pseudo-filesystem.
const MEMMAP_PATH: &str = "/sys/firmware/memmap";

/// The path for reading the physical memory from the mem device.
const PHYS_MEM_PATH: &str = "/dev/mem";

/// Reads the DICE data from the physical memory range starting at the given address.
pub fn read_stage0_dice_data(start: PhysAddr) -> anyhow::Result<Stage0DiceData> {
    let mut result = Stage0DiceData::new_zeroed();
    let buffer = result.as_bytes_mut();
    // Linux presents an inclusive end address.
    let end = start + (buffer.len() as u64 - 1);
    // Ensure that the exact memory range is marked as reserved.
    if !read_memory_ranges()?.iter().any(|range| {
        range.start == start && range.end == end && range.type_description == EXPECTED_E820_TYPE
    }) {
        anyhow::bail!("DICE data range is not reserved");
    }

    let mut dice_reader = OpenOptions::new()
        .read(true)
        .open(PHYS_MEM_PATH)
        .expect("couldn't open DICE memory device for reading");
    dice_reader
        .seek(std::io::SeekFrom::Start(start.as_u64()))
        .expect("couldn't seek to DICE offset");
    dice_reader
        .read_exact(buffer)
        .expect("couldn't read DICE data");

    if result.magic != STAGE0_MAGIC {
        anyhow::bail!("invalid DICE data");
    }

    Ok(result)
}

fn read_memory_ranges() -> anyhow::Result<Vec<MemoryRange>> {
    read_dir(MEMMAP_PATH)
        .context("memory map not found")?
        .map(|entry| {
            let path = entry?.path();
            let start = try_parse_phys_addr(read_to_string(path.join("start"))?.trim())
                .context("couldn't parse start")?;
            let end = try_parse_phys_addr(read_to_string(path.join("end"))?.trim())
                .context("couldn't parse end")?;
            let type_description = read_to_string(path.join("type"))?.trim().to_string();
            Ok(MemoryRange {
                start,
                end,
                type_description,
            })
        })
        .try_collect()
}
