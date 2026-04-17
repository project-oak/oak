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

use core::{marker::PhantomData, ops::RangeBounds};
use std::fs::{OpenOptions, read_dir, read_to_string};

use anyhow::Context;
use nix::sys::mman::{MapFlags, ProtFlags, mmap, munmap};
use oak_attestation_types::{attester::Attester, util::Serializable};
use oak_dice::evidence::STAGE0_DICE_PROTO_MAGIC;
use x86_64::{
    PhysAddr,
    structures::paging::{PageSize, Size4KiB},
};
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

/// Holds a reference to the Attester data in physical memory.
///
/// Zeroes out the source physical memory on drop.
pub struct SensitiveDataMemory<A> {
    start_ptr: *mut u8,
    attester_ptr: *const u8,
    sensitive_memory_length: usize,
    _phantom: PhantomData<A>,
}

impl<A> SensitiveDataMemory<A>
where
    A: Attester + Serializable,
{
    /// Safety: Caller must ensure that there is only instance of this struct
    /// for a given memory range.
    pub unsafe fn new(
        start: PhysAddr,
        eventlog_start: PhysAddr,
        sensitive_memory_length: usize,
    ) -> anyhow::Result<Self> {
        // Linux presents an inclusive end address.
        let end = start + (sensitive_memory_length as u64 - 1);
        // Ensure that the memory range is in reserved memory.
        anyhow::ensure!(
            read_memory_ranges()?.iter().any(|range| {
                range.type_description == RESERVED_E820_TYPE
                    && range.contains(&start)
                    && range.contains(&end)
            }),
            "DICE data range is not in reserved memory"
        );

        // Open a file representing the physical memory.
        let attester_file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(PHYS_MEM_PATH)
            .context("couldn't open attester memory device for reading")?;

        // Safety: we have checked it is within a reserved region, so the Linux kernel
        // will not use it for anything else.
        let start_ptr = unsafe {
            mmap(
                None,
                sensitive_memory_length.try_into()?,
                ProtFlags::PROT_READ | ProtFlags::PROT_WRITE,
                MapFlags::MAP_SHARED,
                // Pass the file descriptor as reference to avoid closing it.
                Some(&attester_file),
                start.as_u64().try_into()?,
            )?
        };

        // Calculate the attester start pointer using the offset between `start`` and
        // `eventlog_start``. The serialized attester is stored 4 KiB after the start of
        // the event log. The attester region starts with an 8 byte magic number.
        let attester_offset = (eventlog_start.as_u64() - start.as_u64() + Size4KiB::SIZE) as usize;

        anyhow::ensure!(
            attester_offset + core::mem::size_of::<u64>() < sensitive_memory_length,
            "serialized attester is not in sensitive memory range"
        );

        // Safety: we have checked that the magic number pointer falls in the sensitive
        // memory range.
        let magic_ptr = unsafe { start_ptr.add(attester_offset) } as *const u64;
        anyhow::ensure!(magic_ptr.is_aligned(), "attester magic number is not properly aligned");
        // Safety: we have checked that the magic number pointer is correctly aligned.
        let magic = unsafe { magic_ptr.read() };
        anyhow::ensure!(magic == STAGE0_DICE_PROTO_MAGIC, "attester magic number is invalid");
        // Note: adding 1 to the pointer adds 8 bytes since points to a `u64`.
        //
        // Safety: we have checked that the data after the magic number pointer falls in
        // the sensitive memory range.
        let attester_ptr = unsafe { magic_ptr.add(1) } as *const u8;

        Ok(Self {
            start_ptr: start_ptr as *mut u8,
            attester_ptr,
            sensitive_memory_length,
            _phantom: PhantomData,
        })
    }

    /// Extracts the serialized attester from the sensitive memory region and
    /// deserializes it.
    pub fn read_into_attester(self) -> anyhow::Result<A> {
        let attester_size = (self.start_ptr as usize + self.sensitive_memory_length)
            .checked_sub(self.attester_ptr as usize)
            .context("invalid attester pointer")?;
        // Safety: We calculated the length to make sure it fits in the sensitive memory
        // range.
        let attester_bytes =
            unsafe { std::slice::from_raw_parts(self.attester_ptr, attester_size) };

        A::deserialize(attester_bytes).context("couldn't deserialize attester")
    }
}

impl<A> Drop for SensitiveDataMemory<A> {
    fn drop(&mut self) {
        // Zero out the sensitive_dice_data_memory.
        // Safety: This struct is only used once. We have checked the length,
        // know it is backed by physical memory and is reserved.
        (unsafe { std::slice::from_raw_parts_mut(self.start_ptr, self.sensitive_memory_length) })
            .zeroize();
        // Safety: We've mapped the memory, this struct is only used once, the only
        // reference to this memory is being dropped.
        unsafe {
            munmap(self.start_ptr as *mut core::ffi::c_void, self.sensitive_memory_length)
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
