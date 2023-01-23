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

/// Tries to load an initial RAM disk from the QEMU FW_CFG device.
///
/// If it finds a RAM disk it returns the address where it is loaded and the size. If not it
/// returns `None`.
pub fn try_load_initial_ram_disk(fw_cfg: &mut FwCfg) -> Option<&[u8]> {
    let size = fw_cfg
        .read_initrd_size()
        .expect("couldn't read initial RAM disk size");
    if size == 0 {
        log::debug!("No initial RAM disk");
        return None;
    }

    let address = fw_cfg
        .read_initrd_address()
        .expect("couldn't read initial RAM disk address");

    log::debug!("Initial RAM disk size {}", size);
    log::debug!("Initial RAM disk address {:#018x}", address.as_u64());

    // TODO(#3628): Check that the suggested address is valid and sensible.
    // Safety: for now we trust that the hypervisor suggests a valid address and to load the RAM
    // disk, but will add checks to ensure it falls in valid mapped memory and won't overwrite
    // existing structures. We only write to the slice and don't assume anything about its layout.
    let buf = unsafe { slice::from_raw_parts_mut::<u8>(address.as_mut_ptr(), size as usize) };
    fw_cfg
        .read_initrd_data(buf)
        .expect("couldn't read initial RAM disk content");
    Some(buf)
}
