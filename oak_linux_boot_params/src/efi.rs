//
// Copyright 2026 The Project Oak Authors
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

//! UEFI 2.11 post-`ExitBootServices()` tables and Linux x86_64 EFI handoff
//! structures for booting with unaccepted memory.
//!
//! Specifications:
//! - UEFI Specification, Version 2.11: <https://uefi.org/specs/UEFI/2.11/>
//! - Linux x86 Zero Page: <https://docs.kernel.org/arch/x86/zero-page.html>

use core::mem::size_of;

use bitflags::bitflags;
use strum::{Display, FromRepr};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, TryFromBytes};

/// Loader signature stored in [`EFIInfo::efi_loader_signature`] for a 64-bit
/// EFI handoff.
///
/// See <https://docs.kernel.org/arch/x86/zero-page.html> and
/// `EFI64_LOADER_SIGNATURE` in Linux `arch/x86/include/asm/efi.h`
/// (<https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/arch/x86/include/asm/efi.h>).
pub const EFI_LOADER_SIGNATURE_64: u32 = u32::from_le_bytes(*b"EL64");

/// EFI handoff block embedded in [`crate::BootParams::efi_info`].
///
/// For a 64-bit handoff, guest physical pointers to [`EfiSystemTable64`] and
/// the [`EfiMemoryDescriptor`] array are split across low and high 32-bit
/// fields.
///
/// See <https://docs.kernel.org/arch/x86/zero-page.html>.
#[repr(C)]
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, FromBytes, IntoBytes, Immutable, KnownLayout,
)]
pub struct EFIInfo {
    /// [`EFI_LOADER_SIGNATURE_64`], or `0` when booting without EFI.
    pub efi_loader_signature: u32,
    /// Lower 32 bits of the [`EfiSystemTable64`] physical address.
    pub efi_systab: u32,
    /// Byte stride of each descriptor in the memory map. Must be non-zero
    /// whenever `efi_loader_signature` is set.
    pub efi_memdesc_size: u32,
    /// Memory descriptor format version ([`EFI_MEMORY_DESCRIPTOR_VERSION`]).
    pub efi_memdesc_version: u32,
    /// Lower 32 bits of the [`EfiMemoryDescriptor`] array physical address.
    pub efi_memmap: u32,
    /// Total byte length of the [`EfiMemoryDescriptor`] array.
    pub efi_memmap_size: u32,
    /// Upper 32 bits of the [`EfiSystemTable64`] physical address.
    pub efi_systab_hi: u32,
    /// Upper 32 bits of the [`EfiMemoryDescriptor`] array physical address.
    pub efi_memmap_hi: u32,
}
static_assertions::assert_eq_size!(EFIInfo, [u8; 32usize]);

impl EFIInfo {
    /// Constructs a 64-bit [`EFIInfo`] for `num_descriptors` entries using
    /// [`EfiMemoryDescriptor`]'s size and [`EFI_MEMORY_DESCRIPTOR_VERSION`].
    ///
    /// # Panics
    ///
    /// Panics if `num_descriptors * size_of::<EfiMemoryDescriptor>()` overflows
    /// `u32`.
    pub const fn new_64bit(
        systab_phys_addr: u64,
        memmap_phys_addr: u64,
        num_descriptors: u32,
    ) -> Self {
        let memdesc_size = size_of::<EfiMemoryDescriptor>() as u32;
        let memmap_size =
            num_descriptors.checked_mul(memdesc_size).expect("memory map byte size overflow");
        Self {
            efi_loader_signature: EFI_LOADER_SIGNATURE_64,
            efi_systab: systab_phys_addr as u32,
            efi_memdesc_size: memdesc_size,
            efi_memdesc_version: EFI_MEMORY_DESCRIPTOR_VERSION,
            efi_memmap: memmap_phys_addr as u32,
            efi_memmap_size: memmap_size,
            efi_systab_hi: (systab_phys_addr >> 32) as u32,
            efi_memmap_hi: (memmap_phys_addr >> 32) as u32,
        }
    }

    /// Reconstructs the 64-bit physical address of [`EfiSystemTable64`].
    pub const fn systab_addr(&self) -> u64 {
        (self.efi_systab as u64) | ((self.efi_systab_hi as u64) << 32)
    }

    /// Reconstructs the 64-bit physical address of the [`EfiMemoryDescriptor`]
    /// array.
    pub const fn memmap_addr(&self) -> u64 {
        (self.efi_memmap as u64) | ((self.efi_memmap_hi as u64) << 32)
    }
}

/// 128-bit mixed-endian UEFI Globally Unique Identifier (`EFI_GUID`).
///
/// `data1`, `data2`, and `data3` are encoded in little-endian byte order while
/// `data4` is stored in big-endian order.
///
/// See Appendix A of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/Apx_A_GUID_and_Time_Formats.html>
#[repr(C, align(4))]
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, FromBytes, IntoBytes, Immutable, KnownLayout,
)]
pub struct EfiGuid {
    data1: u32,
    data2: u16,
    data3: u16,
    data4: [u8; 8],
}
static_assertions::assert_eq_size!(EfiGuid, [u8; 16usize]);

impl EfiGuid {
    /// Creates a mixed-endian UEFI `EFI_GUID` from its canonical components.
    pub const fn new(data1: u32, data2: u16, data3: u16, data4: [u8; 8]) -> Self {
        Self { data1: data1.to_le(), data2: data2.to_le(), data3: data3.to_le(), data4 }
    }
}

/// Configuration table GUID for an ACPI 1.0 RSDP.
///
/// See Section 4.6.1.1 of the UEFI Specification v2.11
/// (<https://uefi.org/specs/UEFI/2.11/04_EFI_System_Table.html#efi-configuration-table-properties-table>)
/// and Section 5.2.5.2 of the ACPI Specification v6.6
/// (<https://uefi.org/specs/ACPI/6.6/05_ACPI_Software_Programming_Model.html#finding-the-rsdp-on-uefi-enabled-systems>).
pub const ACPI_TABLE_GUID: EfiGuid =
    EfiGuid::new(0xeb9d_2d30, 0x2d88, 0x11d3, [0x9a, 0x16, 0x00, 0x90, 0x27, 0x3f, 0xc1, 0x4d]);

/// Configuration table GUID for an ACPI 2.0 or later RSDP.
///
/// See Section 4.6.1.1 of the UEFI Specification v2.11
/// (<https://uefi.org/specs/UEFI/2.11/04_EFI_System_Table.html#efi-configuration-table-properties-table>)
/// and Section 5.2.5.2 of the ACPI Specification v6.6
/// (<https://uefi.org/specs/ACPI/6.6/05_ACPI_Software_Programming_Model.html#finding-the-rsdp-on-uefi-enabled-systems>).
pub const ACPI_20_TABLE_GUID: EfiGuid =
    EfiGuid::new(0x8868_e871, 0xe4f1, 0x11d3, [0xbc, 0x22, 0x00, 0x80, 0xc7, 0x3c, 0x88, 0x81]);

/// Configuration table GUID for the AMD SEV-SNP Confidential Computing blob
/// ([`crate::CCBlobSevInfo`]).
///
/// See <https://docs.kernel.org/arch/x86/zero-page.html> and
/// `CONFIDENTIAL_COMPUTING_SNP_BLOB_GUID` in Tianocore EDK2:
/// <https://github.com/tianocore/edk2/blob/master/OvmfPkg/Include/Guid/ConfidentialComputingSevSnpBlob.h>
pub const EFI_CC_BLOB_GUID: EfiGuid =
    EfiGuid::new(0x067b_1f5f, 0xcf26, 0x44c5, [0x85, 0x54, 0x93, 0xd7, 0x77, 0x91, 0x2d, 0x42]);

/// Linux-specific configuration table GUID for [`EfiUnacceptedMemoryHeader`].
///
/// See Section 7.2.1 of the UEFI Specification v2.11
/// (<https://uefi.org/specs/UEFI/2.11/07_Services_Boot_Services.html#efi-boot-services-allocatepages>)
/// for unaccepted memory semantics and `LINUX_EFI_UNACCEPTED_MEM_TABLE_GUID` in
/// Linux `include/linux/efi.h`
/// (<https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/linux/efi.h>).
pub const LINUX_EFI_UNACCEPTED_MEM_TABLE_GUID: EfiGuid =
    EfiGuid::new(0xd5d1_de3c, 0x105c, 0x44f9, [0x9e, 0xa9, 0xbc, 0xef, 0x98, 0x12, 0x00, 0x31]);

/// Entry in the 64-bit UEFI Configuration Table array
/// (`EFI_CONFIGURATION_TABLE`) referenced by [`EfiSystemTable64::tables`].
///
/// See Section 4.6 of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/04_EFI_System_Table.html#efi-configuration-table-properties-table>
#[repr(C)]
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, FromBytes, IntoBytes, Immutable, KnownLayout,
)]
pub struct EfiConfigTable64 {
    pub guid: EfiGuid,
    /// Guest physical address (or GUID-defined value) of the table.
    pub table: u64,
}
static_assertions::assert_eq_size!(EfiConfigTable64, [u8; 24usize]);

impl EfiConfigTable64 {
    pub const fn new(guid: EfiGuid, table: u64) -> Self {
        Self { guid, table }
    }
}

/// UEFI 2.11.0 specification revision value for
/// [`EfiSystemTableHeader::revision`].
///
/// The upper 16 bits hold the major version and the lower 16 bits hold
/// `minor * 10 + errata` (minor version in the upper decimal digits and errata
/// level in the ones digit); see Section 4.3.1 of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/04_EFI_System_Table.html#efi-system-table-1>
pub const EFI_2_110_SYSTEM_TABLE_REVISION: u32 = (2 << 16) | 110;

/// Single-value zero type for reserved and padding fields in
/// [`EfiSystemTableHeader`] and [`EfiSystemTable64`].
///
/// See Section 4.2.1 of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/04_EFI_System_Table.html#efi-table-header>
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, Immutable, IntoBytes, KnownLayout, TryFromBytes,
)]
#[repr(u32)]
pub enum ReservedZeroU32 {
    #[default]
    Zero = 0,
}

/// Single-value signature for [`EfiSystemTableHeader`].
///
/// See Section 4.3.1 of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/04_EFI_System_Table.html#efi-system-table-1>
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, Immutable, IntoBytes, KnownLayout, TryFromBytes,
)]
#[repr(u64)]
pub enum EfiSystemTableSignature {
    #[default]
    IbiSyst = u64::from_le_bytes(*b"IBI SYST"),
}

/// Single-value byte size for [`EfiSystemTableHeader`].
///
/// See Section 4.3.1 of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/04_EFI_System_Table.html#efi-system-table-1>
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, Immutable, IntoBytes, KnownLayout, TryFromBytes,
)]
#[repr(u32)]
pub enum EfiSystemTableHeaderSize {
    #[default]
    Size = 120,
}

/// `EFI_TABLE_HEADER` for [`EfiSystemTable64`].
///
/// See Section 4.2.1 of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/04_EFI_System_Table.html#efi-table-header>
#[repr(C)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
pub struct EfiSystemTableHeader {
    pub signature: EfiSystemTableSignature,
    pub revision: u32,
    pub headersize: EfiSystemTableHeaderSize,
    /// IEEE 802.3 CRC32 computed over `headersize` bytes with `crc32` set to 0.
    pub crc32: u32,
    pub reserved: ReservedZeroU32,
}
static_assertions::assert_eq_size!(EfiSystemTableHeader, [u8; 24usize]);

impl EfiSystemTableHeader {
    /// Creates a header for [`EfiSystemTable64`] with the given UEFI
    /// specification revision and `crc32` initialized to `0`.
    pub const fn new(revision: u32) -> Self {
        Self {
            signature: EfiSystemTableSignature::IbiSyst,
            revision,
            headersize: EfiSystemTableHeaderSize::Size,
            crc32: 0,
            reserved: ReservedZeroU32::Zero,
        }
    }
}

/// 64-bit UEFI System Table (`EFI_SYSTEM_TABLE`) referenced by [`EFIInfo`].
///
/// After `ExitBootServices()`, boot-time console fields and `boottime` are `0`.
///
/// See Section 4.3.1 of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/04_EFI_System_Table.html#efi-system-table-1>
#[repr(C)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
pub struct EfiSystemTable64 {
    pub hdr: EfiSystemTableHeader,
    /// Physical address of a NUL-terminated UTF-16LE firmware vendor string.
    pub fw_vendor: u64,
    pub fw_revision: u32,
    pub _pad1: ReservedZeroU32,
    pub con_in_handle: u64,
    pub con_in: u64,
    pub con_out_handle: u64,
    pub con_out: u64,
    pub stderr_handle: u64,
    pub stderr: u64,
    pub runtime: u64,
    pub boottime: u64,
    pub nr_tables: u64,
    /// Physical address of the [`EfiConfigTable64`] array of length
    /// `nr_tables`.
    pub tables: u64,
}
static_assertions::assert_eq_size!(EfiSystemTable64, [u8; 120usize]);

impl EfiSystemTable64 {
    /// Creates a post-`ExitBootServices()` system table with
    /// [`EFI_2_110_SYSTEM_TABLE_REVISION`], zeroed boot-time and runtime
    /// service pointers, and `hdr.crc32` initialized to `0`.
    pub const fn new(fw_vendor: u64, fw_revision: u32, nr_tables: u64, tables: u64) -> Self {
        Self {
            hdr: EfiSystemTableHeader::new(EFI_2_110_SYSTEM_TABLE_REVISION),
            fw_vendor,
            fw_revision,
            _pad1: ReservedZeroU32::Zero,
            con_in_handle: 0,
            con_in: 0,
            con_out_handle: 0,
            con_out: 0,
            stderr_handle: 0,
            stderr: 0,
            runtime: 0,
            boottime: 0,
            nr_tables,
            tables,
        }
    }
}

/// Page size in bytes used by [`EfiMemoryDescriptor::num_pages`].
///
/// See Section 7.2.1 of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/07_Services_Boot_Services.html#efi-boot-services-allocatepages>
pub const EFI_PAGE_SIZE: u64 = 4096;

/// Descriptor format version stored in [`EFIInfo::efi_memdesc_version`].
///
/// See Section 7.2.3 of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/07_Services_Boot_Services.html#efi-boot-services-getmemorymap>
pub const EFI_MEMORY_DESCRIPTOR_VERSION: u32 = 1;

/// UEFI memory region types (`EFI_MEMORY_TYPE`).
///
/// See Section 7.2.1 of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/07_Services_Boot_Services.html#efi-boot-services-allocatepages>
#[derive(Copy, Clone, Debug, PartialEq, Eq, Display, FromRepr)]
#[repr(u32)]
pub enum EfiMemoryType {
    /// Not usable by the OS.
    ReservedMemoryType = 0,
    LoaderCode = 1,
    LoaderData = 2,
    BootServicesCode = 3,
    BootServicesData = 4,
    RuntimeServicesCode = 5,
    RuntimeServicesData = 6,
    /// Free pre-accepted RAM usable immediately by the OS.
    ConventionalMemory = 7,
    /// Memory in which hardware errors were detected.
    UnusableMemory = 8,
    /// Memory holding ACPI tables reclaimable after OS ACPI initialization.
    AcpiReclaimMemory = 9,
    /// Firmware-reserved ACPI Non-Volatile Sleeping memory.
    AcpiMemoryNvs = 10,
    MemoryMappedIo = 11,
    MemoryMappedIoPortSpace = 12,
    /// Processor-reserved firmware code.
    PalCode = 13,
    /// Byte-addressable non-volatile memory.
    PersistentMemory = 14,
    /// Private guest RAM that must be accepted via the confidential-computing
    /// architecture before first access and tracked in
    /// [`EfiUnacceptedMemoryHeader`].
    UnacceptedMemoryType = 15,
}

/// Memory capability, cacheability, protection, and runtime attributes for
/// [`EfiMemoryDescriptor::attribute`].
///
/// See Section 7.2.3 of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/07_Services_Boot_Services.html#efi-boot-services-getmemorymap>
#[repr(transparent)]
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, FromBytes, IntoBytes, Immutable, KnownLayout,
)]
pub struct EfiMemoryAttributes(u64);

bitflags! {
    impl EfiMemoryAttributes: u64 {
        /// Uncacheable.
        const UC = 1 << 0;
        /// Write-combining.
        const WC = 1 << 1;
        /// Write-through.
        const WT = 1 << 2;
        /// Write-back cacheable.
        const WB = 1 << 3;
        /// Uncacheable, exported, and supports fetch-and-add.
        const UCE = 1 << 4;
        /// Write-protected.
        const WP = 1 << 12;
        /// Read-protected.
        const RP = 1 << 13;
        /// Execute-protected (non-executable).
        const XP = 1 << 14;
        /// Non-volatile.
        const NV = 1 << 15;
        /// Higher reliability relative to standard main memory.
        const MORE_RELIABLE = 1 << 16;
        /// Read-only.
        const RO = 1 << 17;
        /// Specific-purpose / soft-reserved memory. Must remain clear on
        /// general-purpose [`EfiMemoryType::UnacceptedMemoryType`] ranges.
        const SP = 1 << 18;
        /// Capable of CPU memory encryption.
        const CPU_CRYPTO = 1 << 19;
        /// Capable of runtime hot-unplug.
        const HOT_PLUGGABLE = 1 << 20;
        /// Requires a virtual mapping for UEFI Runtime Services.
        const RUNTIME = 1 << 63;
    }
}

/// UEFI memory map descriptor (`EFI_MEMORY_DESCRIPTOR`) referenced by
/// [`EFIInfo`].
///
/// `type_` is stored as a raw `u32` (covering OEM/OS-reserved ranges
/// `0x7000_0000..=0xffff_ffff`) so any descriptor slice satisfies
/// [`FromBytes`]; use [`Self::memory_type`] to decode standard
/// [`EfiMemoryType`] values.
///
/// See Section 7.2.3 of the UEFI Specification v2.11:
/// <https://uefi.org/specs/UEFI/2.11/07_Services_Boot_Services.html#efi-boot-services-getmemorymap>
#[repr(C)]
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, FromBytes, IntoBytes, Immutable, KnownLayout,
)]
pub struct EfiMemoryDescriptor {
    pub type_: u32,
    pub pad: u32,
    pub phys_addr: u64,
    pub virt_addr: u64,
    /// Number of [`EFI_PAGE_SIZE`] pages in the region.
    pub num_pages: u64,
    pub attribute: EfiMemoryAttributes,
}
static_assertions::assert_eq_size!(EfiMemoryDescriptor, [u8; 40usize]);

impl EfiMemoryDescriptor {
    /// Creates a boot-time descriptor (`pad = 0`, `virt_addr = 0`).
    pub const fn new(
        memory_type: EfiMemoryType,
        phys_addr: u64,
        num_pages: u64,
        attribute: EfiMemoryAttributes,
    ) -> Self {
        Self { type_: memory_type as u32, pad: 0, phys_addr, virt_addr: 0, num_pages, attribute }
    }

    /// Decodes [`Self::type_`] into [`EfiMemoryType`], returning `None` for
    /// unrecognized or OEM/OS-reserved values.
    pub fn memory_type(&self) -> Option<EfiMemoryType> {
        EfiMemoryType::from_repr(self.type_)
    }
}

/// Single-value format version for [`EfiUnacceptedMemoryHeader`].
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, Immutable, IntoBytes, KnownLayout, TryFromBytes,
)]
#[repr(u32)]
pub enum EfiUnacceptedMemoryVersion {
    #[default]
    V1 = 1,
}

/// Granularity in bytes (`PMD_SIZE` on x86_64) covered by each bit in the
/// bitmap trailing [`EfiUnacceptedMemoryHeader`].
///
/// See `EFI_UNACCEPTED_UNIT_SIZE` in Linux `arch/x86/include/asm/efi.h`:
/// <https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/arch/x86/include/asm/efi.h>
pub const EFI_UNACCEPTED_UNIT_SIZE: u32 = 2 * 1024 * 1024;

/// Header of Linux's `struct efi_unaccepted_memory` configuration table
/// ([`LINUX_EFI_UNACCEPTED_MEM_TABLE_GUID`]).
///
/// Immediately followed in guest memory by a contiguous little-endian `u64`
/// bitmap of `size` bytes (`size` should be a multiple of `8`). Bit `i` (`word
/// = i / 64`, `mask = 1u64 << (i % 64)`) is `1` when `[phys_base + i *
/// unit_size, phys_base + (i + 1) * unit_size)` has not yet been accepted;
/// Linux clears bits in place as memory is accepted.
///
/// See Section 7.2.1 of the UEFI Specification v2.11
/// (<https://uefi.org/specs/UEFI/2.11/07_Services_Boot_Services.html#efi-boot-services-allocatepages>)
/// and `struct efi_unaccepted_memory` in Linux `include/linux/efi.h`
/// (<https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/linux/efi.h>).
#[repr(C)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
pub struct EfiUnacceptedMemoryHeader {
    pub version: EfiUnacceptedMemoryVersion,
    pub unit_size: u32,
    /// Guest physical address corresponding to bit `0` of the trailing bitmap.
    pub phys_base: u64,
    /// Byte length of the trailing bitmap.
    pub size: u64,
}
static_assertions::assert_eq_size!(EfiUnacceptedMemoryHeader, [u8; 24usize]);

impl EfiUnacceptedMemoryHeader {
    /// Creates a header with `unit_size` set to [`EFI_UNACCEPTED_UNIT_SIZE`].
    pub const fn new(phys_base: u64, bitmap_size_bytes: u64) -> Self {
        Self {
            version: EfiUnacceptedMemoryVersion::V1,
            unit_size: EFI_UNACCEPTED_UNIT_SIZE,
            phys_base,
            size: bitmap_size_bytes,
        }
    }
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;

    use super::*;
    #[gtest]
    fn efi_guid_and_config_table_encode_mixed_endian_wire_bytes() {
        expect_that!(
            ACPI_TABLE_GUID.as_bytes(),
            eq(&[
                0x30u8, 0x2d, 0x9d, 0xeb, 0x88, 0x2d, 0xd3, 0x11, 0x9a, 0x16, 0x00, 0x90, 0x27,
                0x3f, 0xc1, 0x4d,
            ][..])
        );
        expect_that!(
            ACPI_20_TABLE_GUID.as_bytes(),
            eq(&[
                0x71u8, 0xe8, 0x68, 0x88, 0xf1, 0xe4, 0xd3, 0x11, 0xbc, 0x22, 0x00, 0x80, 0xc7,
                0x3c, 0x88, 0x81,
            ][..])
        );
        expect_that!(
            EFI_CC_BLOB_GUID.as_bytes(),
            eq(&[
                0x5fu8, 0x1f, 0x7b, 0x06, 0x26, 0xcf, 0xc5, 0x44, 0x85, 0x54, 0x93, 0xd7, 0x77,
                0x91, 0x2d, 0x42,
            ][..])
        );

        let unaccepted_wire = [
            0x3cu8, 0xde, 0xd1, 0xd5, 0x5c, 0x10, 0xf9, 0x44, 0x9e, 0xa9, 0xbc, 0xef, 0x98, 0x12,
            0x00, 0x31,
        ];
        expect_that!(LINUX_EFI_UNACCEPTED_MEM_TABLE_GUID.as_bytes(), eq(&unaccepted_wire[..]));

        let cfg = EfiConfigTable64::new(LINUX_EFI_UNACCEPTED_MEM_TABLE_GUID, 0x07ef_7000);
        let mut expected_cfg_bytes = [0u8; 24];
        expected_cfg_bytes[..16].copy_from_slice(&unaccepted_wire);
        expected_cfg_bytes[16..].copy_from_slice(&0x07ef_7000u64.to_le_bytes());
        expect_that!(cfg.as_bytes(), eq(&expected_cfg_bytes[..]));
        expect_that!(EfiConfigTable64::read_from_bytes(cfg.as_bytes()).ok(), eq(Some(cfg)));
    }

    #[gtest]
    fn efi_info_splits_and_reconstructs_64bit_addresses() {
        let systab_pa = 0x0000_0002_07ff_2000u64;
        let memmap_pa = 0x0000_0001_07ff_3000u64;
        let info = EFIInfo::new_64bit(systab_pa, memmap_pa, 12);

        expect_that!(info.systab_addr(), eq(systab_pa));
        expect_that!(info.memmap_addr(), eq(memmap_pa));
        expect_that!(info.efi_memmap_size, eq(12 * size_of::<EfiMemoryDescriptor>() as u32));

        let decoded = EFIInfo::read_from_bytes(info.as_bytes()).expect("valid EFIInfo bytes");
        expect_that!(decoded, eq(info));
    }
}
