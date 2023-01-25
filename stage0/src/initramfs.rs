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

use crate::fw_cfg::FwCfg;
use core::slice;
use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use x86_64::{
    structures::paging::{PageSize, Size2MiB, Size4KiB},
    PhysAddr, VirtAddr,
};

/// Tries to load an initial RAM disk from the QEMU FW_CFG device.
///
/// If it finds a RAM disk it returns the byte slice where it is loaded. If not it returns `None`.
pub fn try_load_initial_ram_disk(
    fw_cfg: &mut FwCfg,
    e820_table: &[BootE820Entry],
) -> Option<&'static [u8]> {
    let size = fw_cfg
        .read_initrd_size()
        .expect("couldn't read initial RAM disk size") as usize;
    if size == 0 {
        log::debug!("No initial RAM disk");
        return None;
    }

    let mut initrd_address = fw_cfg
        .read_initrd_address()
        .expect("couldn't read initial RAM disk address");

    log::debug!("Initial RAM disk size {}", size);
    log::debug!("Initial RAM disk address {:#018x}", initrd_address.as_u64());

    let kernel_address = fw_cfg
        .read_kernel_address()
        .expect("couldn't read kernel address");
    let kernel_size = fw_cfg
        .read_kernel_size()
        .expect("couldn't read kernel address") as u64;

    log::debug!("Kernel size {}", kernel_size);
    log::debug!("Kernel start address {:#018x}", kernel_address.as_u64());

    if let Err(error) = check_initrd_address(
        initrd_address,
        initrd_address + (size as u64),
        kernel_address,
        kernel_address + kernel_size,
        e820_table,
    ) {
        log::warn!("Unsuitable initial RAM disk address: {}", error);
        initrd_address = find_suitable_initrd_address(size, e820_table)
            .expect("couldn't a find suitable initial RAM disk address");
        log::debug!(
            "Suggested new initial RAM disk address: {:#018x}",
            initrd_address.as_u64()
        );
    }

    // If it is still not a suitable address, just panic.
    check_initrd_address(
        initrd_address,
        initrd_address + size as u64,
        kernel_address,
        kernel_address + kernel_size,
        e820_table,
    )
    .expect("couldn't find a suitable initial RAM disk address");

    // We use an identity mapping for memory.
    let address = VirtAddr::new(initrd_address.as_u64());

    // Safety: We already checked that the slice falls within the mapped virtual memory, is backed
    // by physical memory, does not overlap with the kernel, and does not overlap with the first
    // 2MiB where our important data structures live. It can also not overlap with the firmware ROM
    // image, since that is above the 1GiB upper limit we support. We only write to the slice and
    // don't assume anything about its layout or alignment.
    let buf = unsafe { slice::from_raw_parts_mut::<u8>(address.as_mut_ptr(), size) };
    fw_cfg
        .read_initrd_data(buf)
        .expect("couldn't read initial RAM disk content");
    Some(buf)
}

fn check_initrd_address(
    initrd_start: PhysAddr,
    initrd_end: PhysAddr,
    kernel_start: PhysAddr,
    kernel_end: PhysAddr,
    e820_table: &[BootE820Entry],
) -> Result<(), &'static str> {
    if initrd_start.as_u64() < Size2MiB::SIZE {
        return Err("address falls in the first 2MiB");
    }
    if initrd_start < kernel_end && initrd_end > kernel_start {
        return Err("initial RAM disk overlaps with the kernel");
    }
    if initrd_end.as_u64() > crate::TOP_OF_VIRTUAL_MEMORY {
        return Err("initial RAM disk ends above the mapped virtual memory");
    }
    if !e820_table.iter().any(|entry| {
        entry.entry_type() == Some(E820EntryType::RAM)
            && entry.addr() as u64 <= initrd_start.as_u64()
            && (entry.addr() + entry.size()) as u64 >= initrd_end.as_u64()
    }) {
        return Err("initial RAM disk is not backed by physical memory");
    }

    Ok(())
}

fn find_suitable_initrd_address(
    initrd_size: usize,
    e820_table: &[BootE820Entry],
) -> Result<PhysAddr, &'static str> {
    let padded_size = (initrd_size as u64)
        .checked_next_multiple_of(Size4KiB::SIZE)
        .unwrap();
    // We use the end of the highest section of RAM that is big enough and falls below 1GiB.
    e820_table
        .iter()
        .filter_map(|entry| {
            if entry.entry_type() != Some(E820EntryType::RAM) {
                return None;
            }
            let start = entry.addr() as u64;
            let end = crate::TOP_OF_VIRTUAL_MEMORY.min(start + entry.size() as u64);
            if padded_size.checked_add(start).unwrap() > end {
                return None;
            }

            // Align the start address down in case the end was not aligned.
            Some(PhysAddr::new(end.checked_sub(padded_size).unwrap()).align_down(Size4KiB::SIZE))
        })
        .max_by(PhysAddr::cmp)
        .ok_or("no suitable memory available for the initial RAM disk")
}
