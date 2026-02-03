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

#![no_std]

use core::{
    ffi::{CStr, c_char},
    mem::size_of,
};

use bitflags::bitflags;
use strum::{Display, FromRepr};
use zerocopy::{FromBytes, Immutable, IntoBytes};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Display, FromRepr)]
#[repr(u32)]
/// E820 address range types according to Chapter 15 of the ACPI Specification,
///
/// Version 6.4. See <https://uefi.org/specs/ACPI/6.4/15_System_Address_Map_Interfaces/Sys_Address_Map_Interfaces.html> for more details.
pub enum E820EntryType {
    /// Uninitialized entry in the table. Don't trust the address or size.
    INVALID = 0,
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
    /// Persistent memory: must be handled distinct from conventional volatile
    /// memory.
    PMEM = 7,
}

bitflags! {
    /// Boot protocol option flags.
    pub struct LoadFlags: u8 {
        /// - If `0`, the protected-mode code is loaded at `0x10000`.
        /// - If `1`, the protected-mode code is loaded at `0x100000`.
        const LOADED_HIGH = 1 << 0;
        /// Used internally by the compressed kernel to communicate KASLR status to kernel proper.
        ///
        /// - If `1`, KASLR enabled.
        /// - If `0`, KASLR disabled.
        const KASLR_FLAG = 1 << 1;
        /// Requests the kernel to not write early messages that require accessing the display hardware directly.
        ///
        ///  - If 0, print early messages.
        ///  - If 1, suppress early messages.
        const QUIET_FLAG = 1 << 5;
        #[deprecated]
        const KEEP_SEGMENTS = 1 << 6;
        /// Indicates that the value entered in [`SetupHeader::heap_end_ptr`] is valid.
        ///
        /// If this field is clear, some setup code functionality will be disabled.
        const CAN_USE_HEAP = 1 << 7;
    }

    /// Extended Boot protocol option flags.
    pub struct XLoadFlags: u16 {
        /// This kernel has the legacy 64-bit entry point at `0x200`.
        const XLF_KERNEL_64 = 1 << 0;
        /// The kernel/boot_params/cmdline/ramdisk can be above 4G.
        const XLF_CAN_BE_LOADED_ABOVE_4G = 1 << 1;
        /// The kernel supports the 32-bit EFI handoff entry point given at [`SetupHeader::handover_offset`].
        const XLF_EFI_HANDOVER_32 = 1 << 2;
        /// The kernel supports the 64-bit EFI handoff entry point given at [`SetupHeader::handover_offset`] + `0x200`.
        const XLF_EFI_HANDOVER_64 = 1 << 3;
        /// The kernel supports kexec EFI boot with EFI runtime support.
        const XLF_EFI_KEXEC = 1 << 4;
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Display, FromRepr)]
#[repr(u32)]
pub enum SetupDataType {
    None = 0,
    E820Ext = 1,
    DTB = 2,
    PCI = 3,
    EFI = 4,
    AppleProperties = 5,
    Jailhouse = 6,
    CCBlob = 7,
    IMA = 8,
    RngSeed = 9,
}

#[repr(C, packed)]
#[derive(Clone, Copy, Debug)]
pub struct SetupData {
    pub next: *const SetupData,
    pub type_: SetupDataType,
    pub len: u32,
    // We omit the data field here, as it can't be represented in safe Rust.
}

#[repr(C, packed)]
#[derive(Clone, Copy, Debug)]
pub struct CCSetupData {
    pub header: SetupData,
    pub cc_blob_address: u32,
}

impl CCSetupData {
    pub fn new(cc_blob: *const CCBlobSevInfo) -> Self {
        Self {
            header: SetupData {
                next: core::ptr::null(),
                type_: SetupDataType::CCBlob,
                len: (size_of::<CCSetupData>() - size_of::<SetupData>()) as u32,
            },
            cc_blob_address: (cc_blob as usize).try_into().unwrap(),
        }
    }
}

/// Real-mode Kernel Header.
///
/// For each field, some are information from the kernel to the bootloader
/// ("read"), some are expected to be filled out by the bootloader ("write"),
/// and some are expected to be read and modified by the bootloader ("modify").
///
/// All general purpose boot loaders should write the fields marked
/// (obligatory). Boot loaders who want to load the kernel at a nonstandard
/// address should fill in the fields marked (reloc); other boot loaders can
/// ignore those fields.
///
/// The byte order of all fields is littleendian (this is x86, after all.)
///
/// For more details see the Linux kernel docs:
/// <https://www.kernel.org/doc/html/latest/x86/boot.html#the-real-mode-kernel-header>
#[repr(C, packed)]
#[derive(Debug, Copy, Clone, FromBytes, IntoBytes)]
pub struct SetupHeader {
    /// The size of the setup code in 512-byte sectors.
    ///
    /// Type: read.
    ///
    /// If this field is 0, the real value is 4. The real-mode code consists of
    /// the boot sector (always one 512-byte sector) plus the setup code.
    pub setup_sects: u8,
    /// If this field is nonzero, the root defaults to readonly.
    ///
    /// Type: read.
    ///
    /// The use of this field is deprecated; use the “ro” or “rw” options on the
    /// command line instead.
    #[deprecated]
    pub root_flags: u16,
    /// The size of the protected-mode code in units of 16-byte paragraphs.
    ///
    /// Type: read.
    ///
    /// For protocol versions older than 2.04 this field is only two bytes wide,
    /// and therefore cannot be trusted for the size of a kernel if the
    /// LOAD_HIGH flag is set.
    pub syssize: u32,
    /// DO NOT USE - for bootsect.S use only
    ///
    /// Type: kernel internal.
    ///
    /// This field is obsolete.
    #[deprecated]
    pub ram_size: u16,
    /// Video mode control
    ///
    /// Type: modify (obligatory)
    ///
    /// This value of `vga=<mode>` command line option should be entered into
    /// this field, as it is used by the kernel before the command line is
    /// parsed.
    pub vid_mode: u16,
    /// Default root device number
    ///
    /// Type: modify (optional)
    ///
    /// The default root device device number. The use of this field is
    /// deprecated, use the `root=` option on the command line instead.
    #[deprecated]
    pub root_dev: u16,
    /// 0xAA55 magic number
    ///
    /// Type: read
    ///
    /// This is the closest thing old Linux kernels have to a magic number.
    pub boot_flag: u16,
    /// Jump instruction
    ///
    /// Type: read
    ///
    /// Contains an x86 jump instruction, `0xEB` followed by a signed offset
    /// relative to byte `0x202`. This can be used to determine the size of
    /// the header.
    pub jump: u16,
    /// Magic signature "HdrS"
    ///
    /// Type: read
    ///
    /// Contains the magic number “HdrS” (`0x53726448`).
    pub header: u32,
    /// Boot protocol version supported
    ///
    /// Type: read
    ///
    /// Contains the boot protocol version, in `(major << 8)+minor` format, e.g.
    /// `0x0204` for version 2.04, and `0x0a11` for a hypothetical version
    /// 10.17.
    pub version: u16,
    /// Boot loader hook
    ///
    /// Type: modify (optional)
    ///
    /// See <https://www.kernel.org/doc/html/latest/x86/boot.html#advanced-boot-loader-hooks>
    pub realmode_swtch: u32,
    /// The load-low segment (`0x1000`) (obsolete)
    ///
    /// Type: read
    ///
    /// The load low segment (`0x1000`). Obsolete.
    #[deprecated]
    pub start_sys_seg: u16,
    /// Pointer to kernel version string
    ///
    /// Type: read
    ///
    /// If set to a nonzero value, contains a pointer to a NUL-terminated
    /// human-readable kernel version number string, less `0x200`. This can
    /// be used to display the kernel version to the user. This value should
    /// be less than (`0x200*setup_sects`).
    ///
    /// For example, if this value is set to `0x1c00`, the kernel version number
    /// string can be found at offset `0x1e00` in the kernel file.
    pub kernel_version: u16,
    /// Boot loader identifier
    ///
    /// Type: write (obligatory)
    ///
    /// If your boot loader has an assigned id, enter `0xTV` here, where `T` is
    /// an identifier for the boot loader and `V` is a version number.
    /// Otherwise, enter `0xFF` here.
    ///
    /// For boot loader IDs above `T` = `0xD`, write `T` = `0xE` to this field
    /// and write the extended ID minus `0x10` to the
    /// [`SetupHeader::ext_loader_type`] field. Similarly, the
    /// [`SetupHeader::ext_loader_ver`] field can be used to provide more than
    /// four bits for the bootloader version.
    pub type_of_loader: u8,
    /// Boot protocol option flags
    ///
    /// Type: modify (obligatory)
    pub loadflags: u8,
    /// Move to high memory size (used with hooks)
    ///
    /// Type: modify (obligatory)
    ///
    /// When using protocol 2.00 or 2.01, if the real mode kernel is not loaded
    /// at `0x90000`, it gets moved there later in the loading sequence.
    /// Fill in this field if you want additional data (such as the kernel
    /// command line) moved in addition to the real-mode kernel itself.
    ///
    /// The unit is bytes starting with the beginning of the boot sector.
    ///
    /// This field is can be ignored when the protocol is 2.02 or higher, or if
    /// the real-mode code is loaded at `0x90000`.
    pub setup_move_size: u16,
    /// Boot loader hook
    ///
    /// Type: optional, reloc
    ///
    /// The address to jump to in protected mode. This defaults to the load
    /// address of the kernel, and can be used by the boot loader to
    /// determine the proper load address.
    ///
    /// This field can be modified for two purposes:
    /// - as a boot loader hook
    /// - if a bootloader which does not install a hook loads a relocatable
    ///   kernel at a nonstandard address it will have to modify this field to
    ///   point to the load address.
    pub code32_start: u32,
    /// initrd load address (set by boot loader)
    ///
    /// Type: write (obligatory)
    ///
    /// The 32-bit linear address of the initial ramdisk or ramfs. Leave at zero
    /// if there is no initial ramdisk/ramfs.
    pub ramdisk_image: u32,
    /// initrd size (set by boot loader)
    ///
    /// Type: write (obligatory)
    ///
    /// Size of the initial ramdisk or ramfs. Leave at zero if there is no
    /// initial ramdisk/ramfs.
    pub ramdisk_size: u32,
    /// DO NOT USE - for bootsect.S use only
    ///
    /// Type: obsolete
    #[deprecated]
    pub bootsect_kludge: u32,
    /// Free memory after setup end
    ///
    /// Type: write (optional)
    ///
    /// Set this field to the offset (from the beginning of the real-mode code)
    /// of the end of the setup stack/heap, minus `0x0200`.
    pub heap_end_ptr: u16,
    /// Extended boot loader version
    ///
    /// Type: write (optional)
    ///
    /// This field is used as an extension of the version number in the
    /// type_of_loader field. The total version number is considered to be
    /// `(type_of_loader & 0x0f) + (ext_loader_ver << 4)`.
    ///
    /// The use of this field is boot loader specific. If not written, it is
    /// zero.
    ///
    /// Kernels prior to 2.6.31 did not recognize this field, but it is safe to
    /// write for protocol version 2.02 or higher.
    pub ext_loader_ver: u8,
    /// Extended boot laoder ID
    ///
    /// Type: write (obligatory if `(type_of_loader & 0xf0) == 0xe0`)
    ///
    /// This field is used as an extension of the type number in type_of_loader
    /// field. If the type in type_of_loader is `0xE`, then the actual type
    /// is `(ext_loader_type + 0x10)`.
    ///
    /// This field is ignored if the type in type_of_loader is not 0xE.
    ///
    /// Kernels prior to 2.6.31 did not recognize this field, but it is safe to
    /// write for protocol version 2.02 or higher.
    pub ext_loader_type: u8,
    /// 32-bit pointer to the kernel command line
    ///
    /// Type: write (obligatory)
    ///
    /// Set this field to the linear address of the kernel command line. The
    /// kernel command line can be located anywhere between the end of the
    /// setup heap and `0xA0000`; it does not have to be located in the same
    /// 64K segment as the real-mode code itself.
    ///
    /// Fill in this field even if your boot loader does not support a command
    /// line, in which case you can point this to an empty string (or better
    /// yet, to the string “auto”.) If this field is left at zero, the
    /// kernel will assume that your boot loader does not support the 2.02+
    /// protocol.
    pub cmd_line_ptr: u32,
    /// Highest legal initrd address
    ///
    /// Type: read
    ///
    /// The maximum address that may be occupied by the initial ramdisk/ramfs
    /// contents. For boot protocols 2.02 or earlier, this field is not
    /// present, and the maximum address is `0x37FFFFFF`. (This address is
    /// defined as the address of the highest safe byte, so if your
    /// ramdisk is exactly 131072 bytes long and this field is `0x37FFFFFF`, you
    /// can start your ramdisk at `0x37FE0000`.)
    pub initrd_addr_max: u32,
    /// Physical addr alignment required for kernel
    ///
    /// Type: read/modify (reloc)
    /// Alignment unit required by the kernel (if relocatable_kernel is true.) A
    /// relocatable kernel that is loaded at an alignment incompatible with
    /// the value in this field will be realigned during kernel
    /// initialization.
    ///
    /// Starting with protocol version 2.10, this reflects the kernel alignment
    /// preferred for optimal performance; it is possible for the loader to
    /// modify this field to permit a lesser alignment. See the
    /// [`SetupHeader::min_alignment`] and [`SetupHeader::pref_address`] fields.
    pub kernel_alignment: u32,
    /// Whether kernel is relocatable or not
    ///
    /// Type: read (reloc)
    ///
    /// If this field is nonzero, the protected-mode part of the kernel can be
    /// loaded at any address that satisfies the kernel_alignment field.
    /// After loading, the boot loader must set the code32_start field to
    /// point to the loaded code, or to a boot loader hook.
    pub relocatable_kernel: u8,
    /// Minimum alignment, as a power of two
    ///
    /// Type: read (reloc)
    ///
    /// This field, if nonzero, indicates as a power of two the minimum
    /// alignment required, as opposed to preferred, by the kernel to boot.
    /// If a boot loader makes use of this field, it should update the
    /// kernel_alignment field with the alignment unit desired; typically:
    ///
    /// ``` kernel_alignment = 1 << min_alignment ```
    /// 
    /// There may be a considerable performance cost with an excessively misaligned kernel.
    /// Therefore, a loader should typically try each power-of-two alignment from kernel_alignment
    /// down to this alignment.
    pub min_alignment: u8,
    /// Boot protocol option flags
    ///
    /// Type: read
    pub xloadflags: u16,
    /// Maximum size of the kernel command line
    ///
    /// Type: read
    ///
    /// The maximum size of the command line without the terminating zero. This
    /// means that the command line can contain at most `cmdline_size`
    /// characters. With protocol version 2.05 and earlier, the maximum size
    /// was 255.
    pub cmdline_size: u32,
    /// Hardware subarchitecture
    ///
    /// Type: write, optional
    ///
    /// In a paravirtualized environment the hardware low level architectural
    /// pieces such as interrupt handling, page table handling, and
    /// accessing process control registers needs to be done differently.
    ///
    /// This field allows the bootloader to inform the kernel we are in one one
    /// of those environments.
    pub hardware_subarch: u32,
    /// Subarchitecture-specific data
    ///
    /// Type: write (subarch-dependent)
    ///
    /// A pointer to data that is specific to hardware subarch This field is
    /// currently unused for the default x86/PC environment, do not modify.
    pub hardware_subarch_data: u64,
    /// Offset of kernel payload
    ///
    /// Type: read
    ///
    /// If non-zero then this field contains the offset from the beginning of
    /// the protected-mode code to the payload.
    ///
    /// The payload may be compressed. The format of both the compressed and
    /// uncompressed data should be determined using the standard magic
    /// numbers. The currently supported compression formats are gzip (magic
    /// numbers `1F 8B` or `1F 9E`), bzip2 (magic number `42 5A`), LZMA
    /// (magic number `5D 00`), XZ (magic number `FD 37`), LZ4 (magic number `02
    /// 21`) and ZSTD (magic number `28 B5`). The uncompressed payload is
    /// currently always ELF (magic number `7F 45 4C 46`).
    pub payload_offset: u32,
    /// Length of kernel payload
    ///
    /// Type: read
    pub payload_length: u32,
    /// 64-bit physical pointer to linked list of struct setup_data
    ///
    /// Type: write (special)
    ///
    /// The 64-bit physical pointer to NULL terminated single linked list of
    /// struct setup_data. This is used to define a more extensible boot
    /// parameters passing mechanism.
    pub setup_data: u64,
    /// Preferred loading address
    ///
    /// Type: read (reloc)
    ///
    /// This field, if nonzero, represents a preferred load address for the
    /// kernel. A relocating bootloader should attempt to load at this
    /// address if possible.
    ///
    /// A non-relocatable kernel will unconditionally move itself and to run at
    /// this address.
    pub pref_address: u64,
    /// Linear memory required during initialization
    ///
    /// Type: read
    ///
    /// This field indicates the amount of linear contiguous memory starting at
    /// the kernel runtime start address that the kernel needs before it is
    /// capable of examining its memory map. This is not the same thing as
    /// the total amount of memory the kernel needs to boot, but it can be
    /// used by a relocating boot loader to help select a safe load address for
    /// the kernel.
    pub init_size: u32,
    /// Offset of handover entry point
    ///
    /// Type: read
    ///
    /// This field is the offset from the beginning of the kernel image to the
    /// EFI handover protocol entry point. Boot loaders using the EFI
    /// handover protocol to boot the kernel should jump to this offset.
    pub handover_offset: u32,
    /// Offset of the kernel_info
    ///
    /// Type: read
    ///
    /// This field is the offset from the beginning of the kernel image to the
    /// kernel_info. The kernel_info structure is embedded in the Linux
    /// image in the uncompressed protected mode region.
    pub kernel_info_offset: u32,
}
static_assertions::assert_eq_size!(SetupHeader, [u8; 123usize]);

impl SetupHeader {
    pub fn setup_data(&self) -> *const SetupData {
        self.setup_data as *const SetupData
    }

    pub fn load_flags(&self) -> Option<LoadFlags> {
        LoadFlags::from_bits(self.loadflags)
    }

    pub fn x_load_flags(&self) -> Option<XLoadFlags> {
        XLoadFlags::from_bits(self.xloadflags)
    }

    pub fn ramdisk(&self) -> Option<Ramdisk> {
        let size = self.ramdisk_size;
        match size {
            0 => None,
            _ => {
                let addr = self.ramdisk_image;
                Some(Ramdisk { addr, size })
            }
        }
    }
}

#[repr(C, packed)]
#[derive(Debug, Copy, Clone, FromBytes, IntoBytes, PartialEq, Immutable)]
pub struct BootE820Entry {
    addr: usize,
    size: usize,
    type_: u32,
}

impl BootE820Entry {
    pub fn new(addr: usize, size: usize, type_: E820EntryType) -> Self {
        Self { addr, size, type_: type_ as u32 }
    }

    pub fn entry_type(&self) -> Option<E820EntryType> {
        E820EntryType::from_repr(self.type_)
    }

    pub fn addr(&self) -> usize {
        self.addr
    }

    pub fn set_addr(&mut self, addr: usize) {
        self.addr = addr;
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn set_size(&mut self, size: usize) {
        self.size = size;
    }

    pub fn end(&self) -> usize {
        self.addr + self.size
    }
}

impl Default for BootE820Entry {
    fn default() -> Self {
        // Safety: an all-zeroes BootE820Entry struct is valid.
        unsafe { core::mem::zeroed() }
    }
}

#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
pub struct ScreenInfo {
    pub orig_x: u8,
    pub orig_y: u8,
    pub ext_mem_k: u16,
    pub orig_video_page: u16,
    pub orig_video_mode: u8,
    pub orig_video_cols: u8,
    pub flags: u8,
    pub unused2: u8,
    pub orig_video_ega_bx: u16,
    pub unused3: u16,
    pub orig_video_lines: u8,
    pub orig_video_is_vga: u8,
    pub orig_video_points: u16,
    pub lfb_width: u16,
    pub lfb_height: u16,
    pub lfb_depth: u16,
    pub lfb_base: u32,
    pub lfb_size: u32,
    pub cl_magic: u16,
    pub cl_offset: u16,
    pub lfb_linelength: u16,
    pub red_size: u8,
    pub red_pos: u8,
    pub green_size: u8,
    pub green_pos: u8,
    pub blue_size: u8,
    pub blue_pos: u8,
    pub rsvd_size: u8,
    pub rsvd_pos: u8,
    pub vesapm_seg: u16,
    pub vesapm_off: u16,
    pub pages: u16,
    pub vesa_attributes: u16,
    pub capabilities: u32,
    pub ext_lfb_base: u32,
    pub _reserved: [u8; 2usize],
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct APMBiosInfo {
    pub version: u16,
    pub cseg: u16,
    pub offset: u32,
    pub cseg_16: u16,
    pub dseg: u16,
    pub flags: u16,
    pub cseg_len: u16,
    pub cseg_16_len: u16,
    pub dseg_len: u16,
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct ISTInfo {
    pub signature: u32,
    pub command: u32,
    pub event: u32,
    pub perf_level: u32,
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct SysDescTable {
    pub length: u16,
    pub table: [u8; 14usize],
}

#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
pub struct OLPCOfwHeader {
    pub ofw_magic: u32,
    pub ofw_version: u32,
    pub cif_handler: u32,
    pub irq_desc_table: u32,
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct EFIInfo {
    pub efi_loader_signature: u32,
    pub efi_systab: u32,
    pub efi_memdesc_size: u32,
    pub efi_memdesc_version: u32,
    pub efi_memmap: u32,
    pub efi_memmap_size: u32,
    pub efi_systab_hi: u32,
    pub efi_memmap_hi: u32,
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct EDIDInfo {
    pub dummy: [u8; 128usize],
}

pub struct Ramdisk {
    pub addr: u32,
    pub size: u32,
}

#[repr(C, align(4096))]
#[derive(Copy, Clone, Debug)]
pub struct BootParams {
    pub screen_info: ScreenInfo,
    pub apm_bios_info: APMBiosInfo,
    pub _pad2: [u8; 4usize],
    pub tboot_addr: u64,
    pub ist_info: ISTInfo,
    pub acpi_rsdp_addr: u64,
    pub _pad3: [u8; 8usize],
    #[deprecated]
    pub hd0_info: [u8; 16usize],
    #[deprecated]
    pub hd1_info: [u8; 16usize],
    #[deprecated]
    pub sys_desc_table: SysDescTable,
    pub olpc_ofw_header: OLPCOfwHeader,
    pub ext_ramdisk_image: u32,
    pub ext_ramdisk_size: u32,
    pub ext_cmd_line_ptr: u32,
    pub _pad4: [u8; 112usize],
    pub cc_blob_address: u32,
    pub edid_info: EDIDInfo,
    pub efi_info: EFIInfo,
    pub alt_mem_k: u32,
    pub scratch: u32,
    pub e820_entries: u8,
    pub eddbuf_entries: u8,
    pub edd_mbr_sig_buf_entries: u8,
    pub kbd_status: u8,
    pub secure_boot: u8,
    pub _pad5: [u8; 2usize],
    pub sentinel: u8,
    pub _pad6: [u8; 1usize],
    pub hdr: SetupHeader,
    pub _pad7: [u8; 36usize],
    pub edd_mbr_sig_buffer: [u32; 16usize],
    pub e820_table: [BootE820Entry; 128usize],
    pub _pad8: [u8; 48usize],
    pub _eddbuf: [u8; 492usize],
    pub _pad9: [u8; 276usize],
}
static_assertions::assert_eq_size!(BootParams, [u8; 4096usize]);

impl BootParams {
    pub fn zeroed() -> Self {
        // Safety: an all-zeroes BootParams struct is valid.
        unsafe { core::mem::zeroed() }
    }

    pub fn protocol(&self) -> &'static str {
        "Linux Boot Protocol"
    }

    pub fn e820_table(&self) -> &[BootE820Entry] {
        &self.e820_table[..self.e820_entries as usize]
    }

    pub fn append_e820_entry(&mut self, entry: BootE820Entry) {
        self.e820_table[self.e820_entries as usize] = entry;
        self.e820_entries += 1;
    }

    pub fn insert_e820_entry(&mut self, entry: BootE820Entry, index: u8) {
        if index > self.e820_entries {
            panic!("out of bounds insert");
        }
        for i in (index..self.e820_entries).rev() {
            let i = i as usize;
            self.e820_table[i + 1] = self.e820_table[i];
        }
        self.e820_table[index as usize] = entry;
        self.e820_entries += 1;
    }

    pub fn delete_e820_entry(&mut self, index: u8) {
        if index >= self.e820_entries {
            panic!("out of bounds delete");
        }
        for i in (index + 1)..self.e820_entries {
            let i = i as usize;
            self.e820_table[i - 1] = self.e820_table[i];
        }
        self.e820_entries -= 1;
    }

    pub fn args(&self) -> &CStr {
        if self.hdr.cmdline_size == 0 {
            Default::default()
        } else {
            // Safety: Linux boot protocol expects the pointer to be valid, even if there
            // are no args.
            unsafe { CStr::from_ptr(self.hdr.cmd_line_ptr as *const c_char) }
        }
    }

    pub fn ramdisk(&self) -> Option<Ramdisk> {
        self.hdr.ramdisk()
    }
}

pub const CC_BLOB_SEV_INFO_MAGIC: u32 = 0x45444d41; // 'AMDE'

#[repr(C, packed)]
#[derive(Copy, Clone, Debug)]
pub struct CCBlobSevInfo {
    pub magic: u32,
    pub version: u16,
    pub _reserved: u16,
    pub secrets_phys: usize,
    pub secrets_len: u32,
    pub _rsvd1: u32,
    pub cpuid_phys: usize,
    pub cpuid_len: u32,
    pub _rsvd2: u32,
}

impl CCBlobSevInfo {
    pub fn new<S, C>(secrets: *const S, cpuid: *const C) -> Self {
        Self {
            magic: CC_BLOB_SEV_INFO_MAGIC,
            version: 1,
            _reserved: 0,
            secrets_phys: secrets as usize,
            secrets_len: size_of::<S>().try_into().unwrap(),
            _rsvd1: 0,
            cpuid_phys: cpuid as usize,
            cpuid_len: size_of::<C>().try_into().unwrap(),
            _rsvd2: 0,
        }
    }
}
