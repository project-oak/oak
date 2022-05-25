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

use strum::{Display, FromRepr};

#[derive(Debug, PartialEq, Eq, Display, FromRepr)]
#[repr(u32)]
/// E820 address range types according to Chapter 15 of the ACPI Specification, Version 6.4.
/// See <https://uefi.org/specs/ACPI/6.4/15_System_Address_Map_Interfaces/Sys_Address_Map_Interfaces.html> for more details.
pub enum E820EntryType {
    /// Available RAM usable by the operating system.
    RAM = 1,
    /// In use or reserved by the system.
    RESERVED = 2,
    /// ACPI Reclaim Memory. Available after the OS reads the ACPI tables.
    ACPI = 3,
    /// ACPI NVS memory; in use or reserved by the system.
    NVS = 4,
    /// Memory in which errors have been detected.
    UNUSABLE = 5,
    /// Memory that is not enabled.
    DISABLED = 6,
    /// Persistent memory: must be handled distinct from conventional volatile memory.
    PMEM = 7,
}

/// Address range descriptor (known as an E820 entry). As the actual data structure may differ
/// between boot protocols, this trait captures the bare minimum of information we need.
pub trait E820Entry {
    /// Address type of this memory range.
    fn entry_type(&self) -> E820EntryType;
    /// Base physical address of the memory range.
    fn addr(&self) -> usize;
    /// Contiguous length, in bytes, of the memory range.
    fn size(&self) -> usize;
}

/// Generic trait for the boot information data structure provided to the kernel from the boot
/// loader.
pub trait BootInfo<E: E820Entry> {
    /// Human-readable name of the boot protocol.
    fn protocol(&self) -> &str;
    /// Slice of address range descriptors representing the memory layout of the machine.
    fn e820_table(&self) -> &[E];
}
