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

use crate::{cmos::Cmos, fw_cfg::FwCfg};
use core::{
    ffi::CStr,
    mem::{size_of, MaybeUninit},
};
use oak_linux_boot_params::{BootE820Entry, BootParams, E820EntryType};
use oak_sev_guest::io::PortFactoryWrapper;

#[link_section = ".boot.zero_page"]
static mut BOOT_ZERO_PAGE: MaybeUninit<BootParams> = MaybeUninit::uninit();

pub fn init_zero_page(
    fw_cfg: &mut FwCfg,
    port_factory: PortFactoryWrapper,
) -> &'static mut BootParams {
    let mut zero_page = unsafe { BOOT_ZERO_PAGE.write(core::mem::zeroed()) };

    // Magic constants.
    // See https://www.kernel.org/doc/html/latest/x86/boot.html#the-real-mode-kernel-header for more details.
    zero_page.hdr.type_of_loader = 0xFF; // loader type undefined
    zero_page.hdr.boot_flag = 0xAA55; // magic number
    zero_page.hdr.header = 0x53726448; // Magic "HdrS" string
    zero_page.hdr.kernel_alignment = 0x1000000; // Magic number from crosvm source.

    // Try to load the E820 table from fw_cfg.
    // Safety: BootE820Entry has the same structure as what qemu uses, and we're limiting
    // ourselves to up to 128 entries.
    let len_bytes = unsafe {
        fw_cfg.read_file_by_name(
            CStr::from_bytes_with_nul(b"etc/e820\0").unwrap(),
            &mut zero_page.e820_table,
        )
    };

    match len_bytes {
        Ok(len_bytes) => {
            zero_page.e820_entries = (len_bytes / size_of::<BootE820Entry>()) as u8;
            zero_page.e820_table[..(zero_page.e820_entries as usize)]
                .sort_unstable_by_key(|x| x.addr());
        }
        Err(err) => {
            log::warn!("Failed to read 'etc/e820': {}, failing back to CMOS", err);

            // We don't support the early reservation entries, so panic if there are any.
            if fw_cfg.read_e820_reservation_table_size().unwrap_or(0) > 0 {
                panic!("QEMU_E820_RESERVATION_TABLE was not empty!");
            }

            build_e820_from_nvram(zero_page, port_factory).expect("failed to read from CMOS");
        }
    };

    for entry in zero_page.e820_table() {
        log::debug!(
            "early E820 entry: [{:#018x}-{:#018x}), len {}, type {}",
            entry.addr(),
            entry.addr() + entry.size(),
            entry.size(),
            entry.entry_type().unwrap()
        );
    }

    zero_page
}

/// Builds an E820 table by reading the low and high memory amount from CMOS.
///
/// The code is largely based on what SeaBIOS is doing (see `qemu_preinit()` and `qemu_cfg_e820()`
/// in <https://github.com/qemu/seabios/blob/b0d61ecef66eb05bd7a4eb7ada88ec5dab06dfee/src/fw/paravirt.c>),
/// but <https://wiki.osdev.org/Detecting_Memory_%28x86%29> is also a good read on the topic.
fn build_e820_from_nvram(
    zero_page: &mut BootParams,
    port_factory: PortFactoryWrapper,
) -> Result<(), &'static str> {
    // Safety: (a) fw_cfg is available, so we're running under QEMU(ish) and (b) there was no
    // pre-built E820 table in fw_cfg; thus, we can reasonably expect CMOS to available, as that's
    // what SeaBIOS would use in that situation to build the E820 table.
    let mut cmos = unsafe { Cmos::new(port_factory) };
    let mut rs = cmos.low_ram_size()?;
    let high = cmos.high_ram_size()?;

    // Time to put all that we know together.
    // First, we'll leave the top 256K just below the 4G mark reserved for the BIOS itself.
    // Second, leave the last 4 pages of low memory as reserved just below the BIOS area as
    // reserved; according to SeaBIOS, KVM stores some data structures there.
    // Thus, the maximum memory we can have under 4G is 0x1_0000_0000 - (44 * 0x1000) = 0xFFFB_C000.
    if rs > 0xFFFB_C000 {
        rs = 0xFFFB_C000;
    };
    zero_page.e820_entries = 2;
    zero_page.e820_table[0] = BootE820Entry::new(0, rs as usize, E820EntryType::RAM);
    zero_page.e820_table[1] = BootE820Entry::new(
        0xFFFB_C000,
        0x1_0000_0000 - 0xFFFB_C000,
        E820EntryType::RESERVED,
    );

    if high > 0 {
        zero_page.e820_entries += 1;
        zero_page.e820_table[2] =
            BootE820Entry::new(0x1_0000_0000, high as usize, E820EntryType::RAM);
    }

    Ok(())
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
