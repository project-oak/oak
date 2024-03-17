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

use core::{ffi::CStr, slice};

use oak_linux_boot_params::BootE820Entry;

use crate::{
    fw_cfg::{check_non_overlapping, find_suitable_dma_address, FwCfg},
    kernel::KernelInfo,
};

/// The file path used by Stage0 to read the initial RAM disk from the fw_cfg
/// device.
const INITIAL_RAM_DISK_FILE_PATH: &[u8] = b"opt/stage0/initramfs\0";

/// Tries to load an initial RAM disk from the QEMU FW_CFG device.
///
/// If it finds a RAM disk it returns the byte slice where it is loaded. If not
/// it returns `None`.
pub fn try_load_initial_ram_disk(
    fw_cfg: &mut FwCfg,
    e820_table: &[BootE820Entry],
    kernel_info: &KernelInfo,
) -> Option<&'static [u8]> {
    let file = fw_cfg.get_initrd_file().or_else(|| {
        let path = CStr::from_bytes_with_nul(INITIAL_RAM_DISK_FILE_PATH).expect("invalid c-string");
        fw_cfg.find(path)
    })?;
    let size = file.size();
    let initrd_address =
        find_suitable_dma_address(size, e820_table).expect("no suitable DMA address available");

    log::debug!("Initial RAM disk size {}", size);
    log::debug!("Initial RAM disk address {:#018x}", initrd_address.as_u64());

    let address = crate::phys_to_virt(initrd_address);

    check_non_overlapping(address, size, kernel_info.start_address, kernel_info.size)
        .expect("initial RAM disk location overlaps with the kernel");

    // Safety: We already checked that the slice falls in a suitable memory range
    // and does not overlap with the kernel. We only write to the slice and
    // don't assume anything about its layout or alignment.
    let buf = unsafe { slice::from_raw_parts_mut::<u8>(address.as_mut_ptr(), size) };
    let actual_size = fw_cfg.read_file(&file, buf).expect("could not read initial RAM disk");
    assert_eq!(actual_size, size, "initial RAM disk size did not match expected size");
    Some(buf)
}
