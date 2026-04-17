//
// Copyright 2024 The Project Oak Authors
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

use core::sync::atomic::{AtomicBool, AtomicU64, Ordering, fence};

use x86_64::structures::paging::{PageSize, Size4KiB};

/// Firmware Mailbox - structure used by the firmware for inter-cpu comms.
///
/// In TDX, this is also called a "TD Mailbox" (TD_MAILBOX).
/// We don't need to 4K-align it (at least for now) as this is usually part
/// of the BIOS, lives in the ROM area, and thus its exact memory address
/// can be defined by a linker script. In TDX, this is declared in its
/// layout.ld file. We 8-byte align it so that os_mailbox_address fits nicely
/// into a single memory read.
#[repr(C)]
pub struct FirmwareMailbox {
    is_address_set: AtomicBool, // Atomic: prevent compiler omitting writes.

    // For performance, add 7 bytes padding so os_mailbox_address fits in one 8-byte block.
    // And to match the structure declared in tdx.s.
    reserved_1: [u8; 7],

    /// OS Mailbox Address. Only valid when is_address_set is true.
    os_mailbox_address: AtomicU64,

    // Fill the rest with 0s and make sure we take all of the page.
    // E.g. in tdx layout.ld, we request 4K exactly (TD_MAILBOX_SIZE).
    reserved_2: [u8; 4080],
}

// A FirmwareMailbox must take exactly one page.
static_assertions::assert_eq_size!(FirmwareMailbox, [u8; Size4KiB::SIZE as usize]);

impl FirmwareMailbox {
    pub const fn new() -> Self {
        Self {
            is_address_set: AtomicBool::new(false),
            reserved_1: [0; 7],
            os_mailbox_address: AtomicU64::new(0u64),
            reserved_2: [0; 4080],
        }
    }

    pub fn set_os_mailbox_address(&mut self, val: u64) {
        assert!(val >= Size4KiB::SIZE, "First page is unmapped, can't contain an OS Mailbox");
        self.os_mailbox_address.store(val, Ordering::SeqCst);
        fence(Ordering::SeqCst); // Prevent compiler or CPU reordering writes.
        self.is_address_set.store(true, Ordering::SeqCst);
    }

    pub fn get_os_mailbox_address(&self) -> Option<u64> {
        if self.is_address_set.load(Ordering::SeqCst) {
            Some(self.os_mailbox_address.load(Ordering::SeqCst))
        } else {
            None
        }
    }
}

impl Default for FirmwareMailbox {
    fn default() -> Self {
        Self::new()
    }
}

/// OS Mailbox - structure used by the OS for inter-cpu comms
///
/// Through this
/// structure, Tthe BSP (main CPU), running OS code, sends commands to the APs
/// (other CPUs), which may be still running firmware (stage0) code, or OS code.
/// Based on UEFI ACPI Specification section 5.2.12.19, table 5.44,
/// https://uefi.org/htmlspecs/ACPI_Spec_6_4_html/05_ACPI_Software_Programming_Model/ACPI_Software_Programming_Model.html#multiprocessor-wakeup-structure
#[repr(C, align(4096))]
#[derive(Copy, Clone, Debug)]
pub struct OsMailbox {
    /// Command issued by OS for AP to perform. 0=noop, 1=wakeup, 2.. reserved.
    command: u16,

    /// Next 2 bytes are reserved.
    reserved_1: u16,

    /// CPU ID of the AP that must respond (only valid when command=1).
    apic_id: u32,

    /// Address AP must jump to on wakeup.
    wakeup_vector: [u8; 8],

    /// Reserved for OS use.
    reserved_os: [u8; 2032],

    /// Reserved for firmware use.
    reserved_firware: [u8; 2048],
}

// OS Mailbox must be exactly fit one 4KiB page. If it's smaller, other things
// could be stored in its memory page. If it's larger, parts of it will spill
// onto the next page.
static_assertions::assert_eq_size!(OsMailbox, [u8; Size4KiB::SIZE as usize]);

impl Default for OsMailbox {
    fn default() -> Self {
        // Safety: an all-zeroes OsMailbox struct is valid.
        unsafe { core::mem::zeroed() }
    }
}
