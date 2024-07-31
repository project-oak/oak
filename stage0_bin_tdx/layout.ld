/*
 * Copyright 2022 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
*/

HIDDEN(TOP = 4096M);
HIDDEN(TD_HOB_SIZE = 8K);
HIDDEN(TD_HOB_START = 0x800000);
HIDDEN(BFV_SIZE = BIOS_SIZE);
/* We assume BIOS_SIZE will be provided externally. */

MEMORY {
    ram_low : ORIGIN = 0, LENGTH = 1M

    td_hob : ORIGIN = TD_HOB_START, LENGTH = TD_HOB_SIZE
    bios : ORIGIN = TOP - BIOS_SIZE, LENGTH = BIOS_SIZE
}

ENTRY(reset_vector)

/* Segment descriptor flags.
 * See Sections 4.7 and 4.8 in AMD64 Architecture Programmer's Manual, Volume 2 for more details.
 */
HIDDEN(SEGMENT_4K = 1 << (32 + 23)); /* G */
HIDDEN(SEGMENT_DEFAULT_32BIT_OP = 1 << (32 + 22)); /* D/B */
HIDDEN(SEGMENT_LONG = 1 << (32 + 21));
HIDDEN(SEGMENT_PRESENT = 1 << (32 + 15)); /* P */
HIDDEN(SEGMENT_USER = 1 << (32 + 12)); /* S */
HIDDEN(SEGMENT_SYSTEM = 1 << (32 + 12)); /* S */
HIDDEN(SEGMENT_CODE = 1 << (32 + 11));
HIDDEN(SEGMENT_CONFORMING = 1 << (32 + 10));
HIDDEN(SEGMENT_WRITABLE = 1 << (32 + 9));
HIDDEN(SEGMENT_ACCESSED = 1 << (32 + 8));

/* Page table flags */
HIDDEN(PAGE_PRESENT = 1 << 0);
HIDDEN(PAGE_WRITABLE = 1 << 1);
HIDDEN(PAGE_SIZE = 1 << 7);

/* Gate descriptor flags */
HIDDEN(DESCRIPTOR_PRESENT = 1 << 47);
HIDDEN(DESCRIPTOR_INTERRUPT_GATE = 0xE << 40);

/* SEV metadata section types; values defined in
 * https://github.com/tianocore/edk2/blob/master/OvmfPkg/ResetVector/X64/OvmfSevMetadata.asm
 */
HIDDEN(SEV_SECTION_UNMEASURED = 0x1);
HIDDEN(SEV_SECTION_SECRET = 0x2);
HIDDEN(SEV_SECTION_CPUID = 0x3);

SECTIONS {
    /* Lowest 1MB of memory (the real mode address space) where we place a lot of our data structures, as
     * that region is usually avoided by OS kernels.
     * For more background, see:
     * https://wiki.osdev.org/Memory_Map_(x86)
     * https://google.github.io/crosvm/appendix/memory_layout.html
     * https://github.com/tianocore/edk2/blob/master/OvmfPkg/OvmfPkgX64.fdf
     *
     * These sections have to be marked NOLOAD, otherwise you risk ending up with a 4GB BIOS image.
     */

    .boot 0x1000 (NOLOAD) : {
        KEEP(*(.boot))
        . = ALIGN(4K);
    } > ram_low

    .ap_text : AT(TOP - 4K) {
        ap_text_start = .;
        *(.ap_text .ap_text.*)
        ap_text_size = . - ap_text_start;
    } > ram_low

    .ap_bss (NOLOAD) : AT (ADDR(.ap_text) + SIZEOF(.ap_text)) {
        ap_bss_start = .;
        *(.ap_bss .ap_bss.*)
        ap_bss_size = . - ap_bss_start;
    } > ram_low

    ASSERT(. <= 0x10000, "AP bootstrap code needs to be in the first 64K")

    .bss (NOLOAD) : {
        bss_start = .;
        /* Include large section (.lbss) to support large code model.
         * See <https://lld.llvm.org/ELF/large_sections.html>.
         */
        *(.bss .bss.* .lbss.*)
        bss_size = . - bss_start;
    } > ram_low

    .data :
    AT ( ADDR (.text) + SIZEOF (.text) ) {
        data_start = .;
        /* Include large section (.ldata) to support large code model.
         * See <https://lld.llvm.org/ELF/large_sections.html>.
         */
        *(.data .data.* .ldata.*)
        data_size = . - data_start;
    } > ram_low

    /* Put the stack just below the EBDA, at the end of 512K. */
    .stack (0x80000 - 32K) (NOLOAD) : {
        . += 32K;
        stack_start = .;
    } > ram_low

    /* EBDA - Extended BIOS Data Area; 128K of memory between [512K, 640K). The RSDP must be within
     * the first KiB of the EBDA.
     */
    .ebda 0x80000 (NOLOAD) : {
        /* Ensure RSDP is always first in the EBDA. */
        KEEP(*(.ebda.rsdp))
        . = ALIGN(1K);
        *(.ebda .ebda.*)
    } > ram_low

    ASSERT(. <= 0xA0000, "EBDA overflow")

    . = ORIGIN(td_hob);
    /* TD HOB */
    .tdx.td_hob ALIGN(TD_HOB_START, 4K) (NOLOAD): {
        . += TD_HOB_SIZE; /* 8KB */
    } > td_hob

    . = ORIGIN(bios);

    /* Create a BFV header + Ffs File header + File section header
     * All area starting here will be measured by TDX module because
     * the attribute is set to EXTENDMR.
     * In stage0 we don't split BFV into two parts because stage0 does
     * not need to comply with UEFI standard. Thus we don't need to set
     * up the SEC core structure which contains the entry point of the
     * Rust code. */
    .bfv_header : AT(TOP - BFV_SIZE) {
        HIDDEN(bfv_start = .);
        /* BFV EFI_FIRMWARE_VOLUME_HEADER : 120 bytes =
         *    56-byte FirmwareVolumeHeader +
         *    16-byte 2xFvBlockMap
         *    24-byte pad_ffs_header
         *    20-byte fv_ext_header
         *    4-byte  padding */
        /* FV header: 16 bytes zero vector */
        QUAD(0)
        QUAD(0)
        /* FV header: 16 bytes EFI_GUID. TDX requires EFI_FIRMWARE_FILE_SYSTEM2_GUID */
        LONG(0x8c8ce578)
        SHORT(0x8a3d)
        SHORT(0x4f1c)
        SHORT(0x3599)
        BYTE(0x89) BYTE(0x61) BYTE(0x85) BYTE(0xc3) BYTE(0x2d) BYTE(0xd3)
        /* FV header: 8 bytes FV length including header.  */
        QUAD(BFV_SIZE)
        /* FV header: 4 bytes FV Signature set to EFI_FVH_SIGNATURE '_FVH' */
        LONG(0x4856465F)
        /* FV header: 4 bytes attributes. https://github.com/confidential-containers/td-shim/blob/main/td-shim/src/fv.rs#L51 */
        LONG(0x0004f6ff)
        /* FV header: 2 bytes header length. We have 2 block map entries so it's 56+16=72 bytes */
        SHORT(0x0048)
        /* FV header: 2 bytes checksum. This checksum guarantees: sum16(72 bytes of header) = 0 */
        /* XXX: update this after any updates to the header */
        SHORT(0xec4f)
        /* FV header: 2 bytes ExtHeaderOffset. 96=0x60 */
        SHORT(0x0060)
        /* FV header: 1 bytes reserved*/
        BYTE(0x00)
        /* FV header: 1 bytes revision*/
        BYTE(0x02)
        /* FvBlockMap 8 x 2 = 16 bytes */
        /* FvBlockMap[0].num_blocks */
        LONG(BFV_SIZE / 0x1000)
        /* FvBlockMap[0].block_length */
        LONG(0x1000)
        /* FvBlockMap[1].num_blocks */
        LONG(0)
        /* FvBlockMap[1].block_length */
        LONG(0)
        /* 72 bytes here */
        /* Pad FFS header 24 bytes */
        /* empty guid */
        LONG(0x0)
        SHORT(0x0)
        SHORT(0x0)
        SHORT(0x0)
        BYTE(0x0) BYTE(0x0) BYTE(0x0) BYTE(0x0) BYTE(0x0) BYTE(0x0)
        /* empty integrity_check */
        BYTE(0x0) BYTE(0x0)
        /* Type: FV_FILETYPE_FFS_PAD */
        BYTE(0xf0)
        /* Attributes */
        BYTE(0x00)
        /* Size https://github.com/confidential-containers/td-shim/blob/main/td-shim/src/fv.rs#L38 */
        BYTE(0x2c) BYTE(0x00) BYTE(0x00)
        /* State */
        BYTE(0x07)
        HIDDEN(bfv_end = .);
        /* 96 bytes here */
        /* FV Extend Header 20 bytes */
        /* FV Extend Header GUID 16 bytes */
        LONG(0x763bed0d)
        SHORT(0xde9f)
        SHORT(0x48f5)
        SHORT(0xf181)
        BYTE(0x3e) BYTE(0x90) BYTE(0xe1) BYTE(0xb1) BYTE(0xa0) BYTE(0x15)
        /* FV Extend Header header size 4 bytes */
        LONG(0x14)
        /* Padding 4 bytes */
        LONG(0x0)
        /* 120 bytes here. End of EFI_FIRMWARE_VOLUME_HEADER */

        /* EFI_FFS_FILE_HEADER 24-bytes
         * See Platform Initialization Specification, Vol. 3
         * 3.2.3 Firmware File. The file is smaller than 16-byte so we
         * only need to use EFI_FFS_FILE_HEADER */
        /* Name: EFI_GUID 16-byte */
        LONG(0x17ed4c9e)
        SHORT(0x05e0)
        SHORT(0x48a6)
        SHORT(0x1da0)
        BYTE(0xfb) BYTE(0x0f) BYTE(0xa9) BYTE(0x1e) BYTE(0x63) BYTE(0x98)
        /* IntegrityCheck: EFI_FFS_INTEGRITY_CHECK 2 byte
         * Calculation: populate Name, Type, Attributes, Size and clear
         * IntegrityCheck and State. then tweak header to make sum8 is
         * zero. finally set integrity_check.file to FFS_FIXED_CHECKSUM
         * and State to state = EFI_FILE_HEADER_CONSTRUCTION |
         * EFI_FILE_HEADER_VALID | EFI_FILE_DATA_VALID;
         * Ref PI Specification Vol. 3 EFI_FFS_INTEGRITY_CHECK
         */
        /* IntegrityCheck.header:  */
        BYTE(0x0d)
        /* IntegrityCheck.file, FFS_FIXED_CHECKSUM */
        /* XXX: set to 0 for checksum calculation. set back to 0xaa then */
        BYTE(0xaa)
        /* Type: EFI_FV_FILETYPE 1 byte, FV_FILETYPE_SECURITY_CORE */
        BYTE(0x03)
        /* Attributes: EFI_FFS_FILE_ATTRIBUTES 1 byte */
        BYTE(0)
        /* Size[3]: UINT8[3], BFV_SIZE - 120 (FV header size) */
        BYTE(0x88) BYTE(0xff) BYTE(0x1f)
        /* State: 0x7 EFI_FFS_FILE_STATE 1-byte */
        /* EFI_FILE_HEADER_CONSTRUCTION | EFI_FILE_HEADER_VALID | EFI_FILE_DATA_VALID */
        /* XXX: set to 0 for checksum calculation. set back to 0x07 then */
        BYTE(0x07)
        /* 120 + 24 = 144 bytes here. End of EFI_FFS_FILE_HEADER */

        /* EFI_COMMON_SECTION_HEADER, 4-byte */
        /* Size[3]: UINT8[3], BFV_SIZE - sizeof(fv header) - sizeof(file header)
         * = 2M - 120 - 24 = 0x1fff70 */
        BYTE(0x70) BYTE(0xff) BYTE(0x1f)
        /* Type: EFI_SECTION_TYPE. TD-shim uses EFI_SECTION_PE32.
         * Our candidates are
         * EFI_SECTION_FIRMWARE_VOLUME_IMAGE (0x17, Spec Vol.3 3.2.5)
         * EFI_SECTION_PE32 (0x10, Spec Vol.3 3.2.5)
         */
        BYTE(0x17) /* SECTION_FIRMWARE_VOLUME_IMAGE */
        /* 120 + 24 + 4 = 148 bytes here. End of EFI_COMMON_SECTION_HEADER */
    } > bios

    ASSERT(. == TOP - BFV_SIZE + 120 + 24 + 4, "wrong BFV header size")

    .rodata : {
        /* Include large section (.lrodata) to support large code model.
         * See <https://lld.llvm.org/ELF/large_sections.html>.
         */
        KEEP(*(.rodata .rodata.* .lrodata.*))
    } > bios

    .text : {
        /* Include large section (.ltext) to support large code model.
         * See <https://lld.llvm.org/ELF/large_sections.html>.
         */
        *(.text .text.* .ltext.*)
        *(.tdx.bootstrap)
        text_end = .;
    } > bios

    /* Everything below this line interacts with 16-bit code, so should be kept as close to the end of the file as
     * possible; max TOP - 32k. */

    .text16 ALIGN(TOP - 4K + SIZEOF(.ap_text), 16) : {
        *(.text16 .text16.*)
    } > bios

    .rodata.gdt ALIGN(8) : {
         /* Null segment */
        QUAD(0)
        /* 64-bit code segment (see Section 4.8.1):
         *  - D=0, as it's ignored when L=1
         *  - L=1 (long mode)
         *  - P=1 (present)
         *  - DPL=00 (ring 0)
         *  - S=1 (user)
         *  - C/D=1 (code)
         *  - C=0
         */
        cs = . - ADDR(.rodata.gdt);
        QUAD(SEGMENT_4K |
             SEGMENT_LONG |
             SEGMENT_PRESENT |
             SEGMENT_USER |
             SEGMENT_CODE |
             SEGMENT_WRITABLE |
             SEGMENT_ACCESSED)
        /* 64-bit data segment (see Section 4.8.2):
         *  - P=1 (present)
         *  - S=1 (user)
         *  - C/D=0 (data)
         * ...and for 32-bit compatibility (see Section 4.7.3):
         *  - G=1 (limit field is in 4K blocks)
         *  - D/S=1 (default operations are 32-bit)
         *  - limit = 0xFFFFF (in 4K blocks because G=1)
         *
         * Although according to the manual in 64-bit mode WRITABLE should be ignored, at least qemu
         * will cause a #GP if we try to load SS with a segment descriptor that doesn't have it set.
         */
        ds = . - ADDR(.rodata.gdt);
        QUAD(SEGMENT_4K |
             SEGMENT_DEFAULT_32BIT_OP |
             SEGMENT_PRESENT |
             SEGMENT_USER |
             SEGMENT_WRITABLE |
             SEGMENT_ACCESSED |
             (0xF << (32 + 16)) | /* Segment Limit [19:16] */
             0xFFFF)              /* Segment Limit [15:0] */
        /* 32-bit code segment, although we only need it for a really short time (see Section 4.7.2):
         *  - G=1 (limit field is in 4K blocks)
         *  - D=1 (default operations are 32-bit)
         *  - P=1 (present)
         *  - S=1 (user)
         *  - C/D=1 (code segment)
         *  - limit = 0xFFFFF (in 4K blocks because G=1)
         */
        cs32 = . - ADDR(.rodata.gdt);
        QUAD(SEGMENT_4K |
             SEGMENT_DEFAULT_32BIT_OP |
             SEGMENT_PRESENT |
             SEGMENT_USER |
             SEGMENT_CODE |
             SEGMENT_WRITABLE |
             SEGMENT_ACCESSED |
             (0xF << (32 + 16)) | /* Segment Limit [19:16] */
             0xFFFF)              /* Segment Limit [15:0] */
    } > bios

    /* 32-bit interrupt table */
    /* See Section 8.2 in AMD64 Architecture Programmer's Manual, Volume 2 for more details. */
    .rodata.idt ALIGN(8) : {
        QUAD(0) /*  0 - #DE */
        QUAD(0) /*  1 - #DB */
        QUAD(0) /*  2 - #NMI */
        QUAD(0) /*  3 - #BP */
        QUAD(0) /*  4 - #OF */
        QUAD(0) /*  5 - #BR */
        QUAD(0) /*  6 - #UD */
        QUAD(0) /*  7 - #NM */
        QUAD(0) /*  8 - #DF */
        QUAD(0) /*  9 - reserved */
        QUAD(0) /* 10 - #TS */
        QUAD(0) /* 11 - #NP */
        QUAD(0) /* 12 - #SS */
        QUAD(   /* 13 - #GP */
            (gp_handler & 0xFFFF0000) << 32 | /* target offset [31:16] */
            DESCRIPTOR_PRESENT |
            DESCRIPTOR_INTERRUPT_GATE |
            cs32 << 16 |                      /* code segment selector */
            gp_handler & 0xFFFF)              /* target offset [15:0] */
        QUAD(0) /* 14 - #PF */
        QUAD(0) /* 15 - reserved */
        QUAD(0) /* 16 - #MF */
        QUAD(0) /* 17 - #AC */
        QUAD(0) /* 18 - #MC */
        QUAD(0) /* 19 - #XF */
        QUAD(0) /* 20 - reserved */
        QUAD(0) /* 21 - #CP */
        QUAD(0) /* 22 - reserved */
        QUAD(0) /* 23 - reserved */
        QUAD(0) /* 24 - reserved */
        QUAD(0) /* 25 - reserved */
        QUAD(0) /* 26 - reserved */
        QUAD(0) /* 27 - reserved */
        QUAD(0) /* 28 - #HV */
        QUAD(   /* 29 - #VC */
            (vc_handler & 0xFFFF0000) << 32 | /* target offset [31:16] */
            DESCRIPTOR_PRESENT |
            DESCRIPTOR_INTERRUPT_GATE |
            cs32 << 16 |                      /* code segment selector */
            vc_handler & 0xFFFF)              /* target offset [15:0] */
        QUAD(0) /* 30 - #SX */
        QUAD(0) /* 31 - reserved */
    } > bios
    
    .rodata.gdt_desc ALIGN(8) : {
        SHORT(SIZEOF(.rodata.gdt) - 1)
        LONG(ADDR(.rodata.gdt))
    } > bios

    .rodata.idt_desc ALIGN(8) : {
        SHORT(SIZEOF(.rodata.idt) - 1)
        LONG(ADDR(.rodata.idt))
    } > bios

    gdt_desc_offset = ADDR(.rodata.gdt_desc);
    idt_desc_offset = ADDR(.rodata.idt_desc);

    /* GUIDed tables have to *end* at 0x20 from the end of the file.
     * Documentation about the GUID table format can be found in QEMU docs:
     * https://github.com/qemu/qemu/blob/master/docs/specs/sev-guest-firmware.rst
     * and EDK2 source code:
     * https://github.com/tianocore/edk2/blob/master/OvmfPkg/ResetVector/Ia16/ResetVectorVtf0.asm
     *
     * Unfortunately it doesn't look like `SIZEOF()` works here, so we have to keep track of the data
     * structure size by hand to ensure that it ends at the correct location in memory.
     */
    .guid_tables TOP - 0x20 - (16             /* AMD SEV header       <--------|     */
                                  + 3*12      /* AMD SEV metadata sections     |     */
                                  + 16        /* Intel TDX metadata GUID       |     */
                                  + 16        /* TDVF decriptor       <--------|--|  */
                                  + 2*32      /* TDVF sections                 |  |  */
                                  + 22        /* AMD SEV metadata offset block |  |  */
                                  + 22        /* AMD SEV-ES reset block           |  */
                                  + 22        /* Intel TDX metadata offset block  |  */
                                  + 18        /* footer */) : {
        /* SEV metadata. This data structure is not part of the GUIDed tables, but it makes sense to have
         * them together at the end of the file, thus we put them in the .guid_tables section along with
         * the GUIDed tables themselves. The data structure is defined in the EDK2 source:
         * https://github.com/tianocore/edk2/blob/master/OvmfPkg/ResetVector/X64/OvmfSevMetadata.asm
         *
         * Size: header is 16 bytes + a number of 12-byte sections.
         */
        HIDDEN(sev_guided_structure_start = .);
        /* Header: uint32 signature ("ASEV"), uint32 length, uint32 version, uint32 number of sections */
        BYTE(0x41) BYTE(0x53) BYTE(0x45) BYTE(0x56)
        LONG(sev_guided_structure_end - sev_guided_structure_start)
        LONG(1)
        LONG((sev_guided_structure_end - sev_guided_structure_start - 16) / 12)
        /* Each section has the basic structure of uint32 address, uint32 length, uint32 type
         * The locations of these pages have been chosen to be the same as EDK2:
         * https://github.com/tianocore/edk2/blob/c05a218a9758225ddf94eedb365633f2154551da/OvmfPkg/OvmfPkgX64.fdf
         * Thankfully none of these clashed with existing data structures that we're setting up.
         */
        /* Unmeasured page location */
        /* We mark the stack as unmeasured, as we need to support interrupts before we even know whether
         * we're running under some form of SEV, and interrupts require a functioning stack.
         */
        LONG(ADDR(.stack))
        LONG(SIZEOF(.stack))
        LONG(SEV_SECTION_UNMEASURED)
        /* Secrets page location */
        LONG(SEV_SECRETS)
        LONG(0x1000)
        LONG(SEV_SECTION_SECRET)
        /* CPUID page location */
        LONG(SEV_CPUID)
        LONG(0x1000)
        LONG(SEV_SECTION_CPUID)
        HIDDEN(sev_guided_structure_end = .);

        /* TDX metadata.
         *
         * See TDX Virtual Firmware Design Guide, chapter 11
         * Size: 16 bytes UUID + 16 bytes descriptor + a number of 32-byte sections.
         * TDX Metadata GUID "e9eaf9f3-168e-44d5-a8eb-7f4d8738f6ae"
         * Hypervisor checks this UUID
         */
        HIDDEN(tdx_metadata_guid = .);
        LONG(0xe9eaf9f3)
        SHORT(0x168e)
        SHORT(0x44d5)
        SHORT(0xeba8)
        BYTE(0x7f) BYTE(0x4d) BYTE(0x87) BYTE(0x38) BYTE(0xf6) BYTE(0xae)
        /* Descriptor: See Table 11-1: TDVF_DESCRIPTOR definition
         * uint32 signature ("TDVF"), uint32 length, uint32 version, uint32 number of sections */
        HIDDEN(tdx_metadata_structure_start = .);
        BYTE(0x54) BYTE(0x44) BYTE(0x56) BYTE(0x46)
        LONG(tdx_metadata_structure_end - tdx_metadata_structure_start)
        LONG(1) /* version, must be 1 */
        LONG((tdx_metadata_structure_end - tdx_metadata_structure_start - 16) / 32)
        /* 32-byte sections to be added: "BFV", "CFV", ...
         * See Table 11-2: TDVF_SECTION definition
         * uint32 offset, uint32 raw data size, uint64 memory base, uint64 memory size, uint32 type, uint32 attributes
         * For example
         * LONG(tdx_bfv_raw_data_offset)
         * LONG(tdx_bfv_raw_data_size)
         * QUAD(tdx_bfv_memory_base)
         * QUAD(tdx_bfv_memory_size)
         * LONG(tdx_metadata_section_type_bfv)
         * LONG(tdx_metadata_attributes_extendmr)
         */
        /* TD HoB */
        LONG(0)
        LONG(0)
        QUAD(TD_HOB_START)
        QUAD(TD_HOB_SIZE)
        LONG(2)                      /* TDX_METADATA_SECTION_TYPE_TD_HOB */
        LONG(0)
        /* TD Boot Firmware Volume (BFV)
         * This area will be marked with EXTENDMR which means the tdx module
         * extend measurement of TD (MR_TD, not RTMRs) with the content of
         * this area. BFV is a UEFI Firmware Volume and has a Firmware Volume
         * header (120 bytes). Right after the FV header we put a Firmware
         * File header to create a firmware file. Next, we put a File Section
         * header to describe a chunk. Since it is smaller than 16MB we can
         * just use EFI_FFS_FILE_HEADER.
        */
        LONG(0x0)                      /* TDX_BFV_RAW_DATA_OFFSET */
        LONG(BFV_SIZE)                     /* TDX_BFV_RAW_DATA_SIZE */
        QUAD(TOP - BFV_SIZE)               /* TDX_BFV_MEMORY_BASE */
        QUAD(BFV_SIZE)                     /* TDX_BFV_MEMORY_SIZE */
        LONG(0)                      /* TDX_METADATA_SECTION_TYPE_BFV */
        LONG(0x00000001)             /* TDX_METADATA_ATTRIBUTES_EXTENDMR */
        HIDDEN(tdx_metadata_structure_end = .);

        /*
         * This is where the GUIDed tables actually start.
         * Size: each entry is 22 bytes + a 18-byte footer.
         */
        HIDDEN(tables_start = .);
        /* SEV metadata descriptor: uint32 offset, uint16 size, 16-byte GUID */
        HIDDEN(sev_metadata_offset_start = .);
        LONG(TOP - sev_guided_structure_start)
        SHORT(sev_metadata_offset_end - sev_metadata_offset_start)
        LONG(0xdc886566)
        SHORT(0x984a)
        SHORT(0x4798)
        SHORT(0x5ea7)
        BYTE(0x55) BYTE(0x85) BYTE(0xa7) BYTE(0xbf) BYTE(0x67) BYTE(0xcc)
        HIDDEN(sev_metadata_offset_end = .);

        /* SEV-ES reset block: uint32 addr, uint16 size, 16-byte GUID */
        HIDDEN(sev_es_reset_block_start = .);
        LONG(sev_es_start)
        SHORT(sev_es_reset_block_end - sev_es_reset_block_start)
        LONG(0x00f771de)
        SHORT(0x1a7e)
        SHORT(0x4fcb)
        SHORT(0x0e89)
        BYTE(0x68) BYTE(0xc7) BYTE(0x7e) BYTE(0x2f) BYTE(0xb4) BYTE(0x4e)
        HIDDEN(sev_es_reset_block_end = .);

        /* TDX metadata offset block: uint32 addr, uint16 size, 16-byte GUID */
        /* https://github.com/tianocore/edk2/blob/master/OvmfPkg/ResetVector/Ia16/ResetVectorVtf0.asm#L58 */
        HIDDEN(tdx_metadata_offset_start = .);
        LONG(TOP - tdx_metadata_structure_start) /* points to Descriptor */
        SHORT(tdx_metadata_offset_end - tdx_metadata_offset_start)
        LONG(0xe47a6535)
        SHORT(0x984a)
        SHORT(0x4798)
        SHORT(0x5e86)
        BYTE(0x46) BYTE(0x85) BYTE(0xa7) BYTE(0xbf) BYTE(0x8e) BYTE(0xc2)
        HIDDEN(tdx_metadata_offset_end = .);

        /* Footer: uint16 size, 16-byte GUID */
        SHORT(tables_end - tables_start)
        LONG(0x96b582de)
        SHORT(0x1fb2)
        SHORT(0x45f7)
        SHORT(0xeaba)
        BYTE(0xa3) BYTE(0x66) BYTE(0xc5) BYTE(0x5a) BYTE(0x08) BYTE(0x2d)
        HIDDEN(tables_end = .);
    } > bios

    ASSERT((. == TOP - 0x20), "GUID tables are to expected to end at top - 0x20")

    /* The reset vector needs to be placed 0x10 from the end of the file. */
    .reset_vector TOP - 0x10 : {
        *(.reset_vector)
        FILL(0x00)
        . = TOP;
    } > bios

    /DISCARD/ : {
        *(.eh_frame)
        *(.comment*)
    }
}