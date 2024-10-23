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
static_assertions::assert_eq_size!(OsMailbox, [u8; 4096usize]);

impl Default for OsMailbox {
    fn default() -> Self {
        // Safety: an all-zeroes OsMailbox struct is valid.
        unsafe { core::mem::zeroed() }
    }
}
