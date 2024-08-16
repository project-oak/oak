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

use core::ops::RangeBounds;
use std::fs::{read_dir, read_to_string, OpenOptions};

use anyhow::Context;
use ciborium::Value;
use coset::cwt::ClaimName;
use nix::sys::mman::{mmap, munmap, MapFlags, ProtFlags};
use oak_attestation::dice::{stage0_dice_data_to_proto, DiceBuilder};
use oak_dice::{
    cert::{LAYER_2_CODE_MEASUREMENT_ID, SHA2_256_ID, SYSTEM_IMAGE_LAYER_ID},
    evidence::STAGE0_MAGIC,
};
use oak_proto_rust::oak::attestation::v1::DiceData;
use sha2::{Digest, Sha256};
use x86_64::PhysAddr;
use zerocopy::FromBytes;
use zeroize::Zeroize;

use crate::try_parse_phys_addr;

/// The expected string representation for reserved memory.
///
/// The text is defined in
/// <https://github.com/torvalds/linux/blob/d88520ad73b79e71e3ddf08de335b8520ae41c5c/arch/x86/kernel/e820.c#L1086>.
const RESERVED_E820_TYPE: &str = "Reserved";

/// The path for reading the memory map from the sysfs pseudo-filesystem.
const MEMMAP_PATH: &str = "/sys/firmware/memmap";

/// The path for reading the physical memory from the mem device.
const PHYS_MEM_PATH: &str = "/dev/mem";

/// Measures the downloaded system image bytes and returns it as a vector of
/// additional CWT claims.
pub fn measure_system_image(system_image_bytes: &[u8]) -> Vec<(ClaimName, Value)> {
    let mut digest = Sha256::default();
    digest.update(system_image_bytes);
    let digest = digest.finalize();
    vec![(
        ClaimName::PrivateUse(SYSTEM_IMAGE_LAYER_ID),
        Value::Map(vec![(
            Value::Integer(LAYER_2_CODE_MEASUREMENT_ID.into()),
            Value::Map(vec![(
                Value::Integer(SHA2_256_ID.into()),
                Value::Bytes(digest[..].to_vec()),
            )]),
        )]),
    )]
}

#[derive(Debug)]
struct MemoryRange {
    start: PhysAddr,
    end: PhysAddr,
    type_description: String,
}

impl core::ops::RangeBounds<PhysAddr> for MemoryRange {
    fn start_bound(&self) -> core::ops::Bound<&PhysAddr> {
        core::ops::Bound::Included(&self.start)
    }
    fn end_bound(&self) -> core::ops::Bound<&PhysAddr> {
        core::ops::Bound::Included(&self.end)
    }
}

/// Holds a reference to the DICE data in physical memory.
///
/// Zeroes out the source physical memory on drop.
pub struct SensitiveDiceDataMemory {
    start_ptr: *mut u8,
    length: usize,
}

impl SensitiveDiceDataMemory {
    /// Safety: Caller must ensure that there is only instance of this struct.
    pub unsafe fn new(start: PhysAddr, length: Option<usize>) -> anyhow::Result<Self> {
        // Indicates the length of the DICE data that needs to be zeroed to delete
        // the layer1 certificate authority from memory. Older versions of stage0 do not
        // send it, then we default to the length of the relevant struct.
        let length = length
            .inspect(|&l| {
                assert!(
                    l >= core::mem::size_of::<oak_dice::evidence::Stage0DiceData>(),
                    "the cmdline argument for dice data length must be no less than the size of the Stage0DiceData struct"
                );
            })
            .unwrap_or_else(|| core::mem::size_of::<oak_dice::evidence::Stage0DiceData>());

        // Linux presents an inclusive end address.
        let end = start + (length as u64 - 1);
        // Ensure that the memory range is in reserved memory.
        anyhow::ensure!(
            read_memory_ranges()?.iter().any(|range| range.type_description == RESERVED_E820_TYPE
                && range.contains(&start)
                && range.contains(&end)),
            "DICE data range is not in reserved memory"
        );

        // Open a file representing the physical memory.
        let dice_file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(PHYS_MEM_PATH)
            .context("couldn't open DICE memory device for reading")?;

        // Safety: we have checked it is within a reserved region, so the Linux kernel
        // will not use it for anything else.
        let start_ptr = unsafe {
            mmap(
                None,
                length.try_into()?,
                ProtFlags::PROT_READ | ProtFlags::PROT_WRITE,
                MapFlags::MAP_SHARED,
                // Pass the file descriptor as reference to avoid closing it.
                Some(&dice_file),
                start.as_u64().try_into()?,
            )?
        };

        Ok(Self { start_ptr: start_ptr as *mut u8, length })
    }

    /// Extracts the DICE evidence and ECA key from the Stage 0 DICE data
    /// located at the given physical address.
    fn read_stage0_dice_data(&self) -> Result<oak_dice::evidence::Stage0DiceData, anyhow::Error> {
        let struct_slice = {
            // Safety: We have checked the length, know it is backed by physical memory.
            unsafe {
                std::slice::from_raw_parts(
                    self.start_ptr,
                    core::mem::size_of::<oak_dice::evidence::Stage0DiceData>(),
                )
            }
        };
        oak_dice::evidence::Stage0DiceData::read_from(&struct_slice)
            .ok_or_else(|| anyhow::anyhow!("size mismatch while reading DICE data"))
            .and_then(|result| {
                if result.magic != STAGE0_MAGIC {
                    Err(anyhow::Error::msg("invalid DICE data"))
                } else {
                    Ok(result)
                }
            })
    }

    /// Extracts the DICE evidence and ECA key from the Stage 0 DICE data
    /// located at the given physical address.
    pub fn read_into_dice_builder(self) -> anyhow::Result<DiceBuilder> {
        let stage0_dice_data = self.read_stage0_dice_data()?;
        let dice_data: DiceData = stage0_dice_data_to_proto(stage0_dice_data)?;
        dice_data.try_into()
    }
}

impl Drop for SensitiveDiceDataMemory {
    fn drop(&mut self) {
        // Zero out the sensitive_dice_data_memory.
        // Safety: This struct is only used once. We have checked the length,
        // know it is backed by physical memory and is reserved.
        (unsafe { std::slice::from_raw_parts_mut(self.start_ptr, self.length) }).zeroize();
        // Safety: We've mapped the memory, this struct is only used once, the only
        // reference to this memory is being dropped.
        unsafe {
            munmap(self.start_ptr as *mut core::ffi::c_void, self.length)
                .expect("Failed to unmap layer0 dice memory")
        };
    }
}

/// Reads the memory ranges which supplied by the firmware to the Linux kernel.
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
            Ok(MemoryRange { start, end, type_description })
        })
        .try_collect()
}
