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

use crate::fw_cfg::FwCfg;
use core::{
    ffi::CStr,
    mem::{size_of, MaybeUninit},
};
use oak_linux_boot_params::{BootE820Entry, BootParams};

#[link_section = ".boot.zero_page"]
static mut BOOT_ZERO_PAGE: MaybeUninit<BootParams> = MaybeUninit::uninit();

pub fn init_zero_page(fw_cfg: &mut FwCfg) -> &'static mut BootParams {
    let mut zero_page = unsafe { BOOT_ZERO_PAGE.write(core::mem::zeroed()) };

    // Magic constants.
    // See https://www.kernel.org/doc/html/latest/x86/boot.html#the-real-mode-kernel-header for more details.
    zero_page.hdr.type_of_loader = 0xFF; // loader type undefined
    zero_page.hdr.boot_flag = 0xAA55; // magic number
    zero_page.hdr.header = 0x53726448; // Magic "HdrS" string
    zero_page.hdr.kernel_alignment = 0x1000000; // Magic number from crosvm source.

    // Load the E820 table from fw_cfg.
    // Safety: BootE820Entry has the same structure as what qemu uses, and we're limiting
    // ourselves to up to 128 entries.
    let len_bytes = unsafe {
        fw_cfg.read_file_by_name(
            CStr::from_bytes_with_nul(b"etc/e820\0").unwrap(),
            &mut zero_page.e820_table,
        )
    }
    .unwrap();
    zero_page.e820_entries = (len_bytes / size_of::<BootE820Entry>()) as u8;

    for entry in zero_page.e820_table() {
        log::debug!(
            "early E820 entry: start {:#018x}, len {}, type {}",
            entry.addr(),
            entry.size(),
            entry.entry_type().unwrap()
        );
    }

    zero_page
}

/// Returns a mutable reference to the zero page, which we assume is initialized.
///
/// # Safety
///
/// This assumes the VMM has set up the zero page for us. Calling this function without the memory
/// set up correctly is undefined behaviour.
pub unsafe fn get_zero_page() -> &'static mut BootParams {
    BOOT_ZERO_PAGE.assume_init_mut()
}
