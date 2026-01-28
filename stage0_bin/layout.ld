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
/* We assume BIOS_SIZE will be provided externally. */

MEMORY {
    ram_low : ORIGIN = 0, LENGTH = 1M

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
HIDDEN(SEV_SECTION_KERNEL_HASHES = 0x10);

/*
 * LD doesn't follow the order of the layout script when placing segments without explicit phdrs
 * defined, so we define all the phdrs explicitly.
 */
PHDRS
{
    boot PT_LOAD;
    ap_text PT_LOAD;
    ap_bss PT_LOAD;
    snp_hash_table PT_LOAD;
    bss PT_LOAD;
    data PT_LOAD;
    stack PT_LOAD;
    ebda PT_LOAD;
    rodata PT_LOAD;
    text PT_LOAD;
    descriptors PT_LOAD;
    text16 PT_LOAD;
    guid_tables PT_LOAD;
    descriptors PT_LOAD;
    reset_vector PT_LOAD;
}

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
    } > ram_low : boot

    .ap_text : AT(TOP - 4K) {
        ap_text_start = .;
        *(.ap_text .ap_text.*)
    } > ram_low : ap_text
    ap_text_size = SIZEOF(.ap_text);

    .ap_bss (NOLOAD) : AT (ADDR(.ap_text) + SIZEOF(.ap_text)) {
        ap_bss_start = .;
        *(.ap_bss .ap_bss.*)
    } > ram_low : ap_bss
    ap_bss_size = SIZEOF(.ap_bss);

    ASSERT(. <= 0x10000, "AP bootstrap code needs to be in the first 64K")

    /* Linkable in the bootloader
     * UEFI hardcodes this address and table size:
     * https://github.com/tianocore/edk2/blob/f98662c5e35b6ab60f46ee4350fa0e6eab0497cf/OvmfPkg/Include/Fdf/MemFd.fdf.inc#L89-L93
     */
    .snp_hash_table 0x10c00 (NOLOAD) : {
       . += 0x400; /* 1k */
    } > ram_low : snp_hash_table

    .bss (NOLOAD) : {
        bss_start = .;
        /* Include large section (.lbss) to support large code model.
         * See <https://lld.llvm.org/ELF/large_sections.html>.
         */
        *(.bss .bss.* .lbss.*)
    } > ram_low : bss
    bss_size = SIZEOF(.bss);

    .rodata : {
        /* Include large section (.lrodata) to support large code model.
         * See <https://lld.llvm.org/ELF/large_sections.html>.
         */
        KEEP(*(.rodata .rodata.* .lrodata.*))
    } > bios : rodata

    .text : {
        /* Include large section (.ltext) to support large code model.
         * See <https://lld.llvm.org/ELF/large_sections.html>.
         */
        *(.text .text.* .ltext.*)
        text_end = .;
    } > bios : text

    .data :
    AT ( ADDR (.text) + SIZEOF (.text) ) {
        data_start = .;
        /* Include large section (.ldata) to support large code model.
         * See <https://lld.llvm.org/ELF/large_sections.html>.
         */
        *(.data .data.* .ldata.*)
    } > ram_low : data
    data_size = SIZEOF(.data);

    /* Put the stack just below the EBDA, at the end of 512K. */
    .stack (0x80000 - 32K) (NOLOAD) : {
        . += 32K;
        stack_start = .;
    } > ram_low : stack

    /* EBDA - Extended BIOS Data Area; 128K of memory between [512K, 640K). The RSDP must be within
     * the first KiB of the EBDA.
     */
    .ebda 0x80000 (NOLOAD) : {
        *(.ebda .ebda.*)
    } > ram_low : ebda

    ASSERT(. <= 0xA0000, "EBDA overflow")

    /* Everything below this line interacts with 16-bit code, so should be kept as close to the end of the file as
     * possible; max TOP - 32k. */

    .text16 ALIGN(TOP - 4K + SIZEOF(.ap_text), 16) : {
        *(.text16 .text16.*)
    } > bios : text16

    .gdt ALIGN(8) : {
        HIDDEN(gdt_start = ABSOLUTE(.));
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
        cs = (. - gdt_start);
        QUAD(SEGMENT_LONG |
             SEGMENT_PRESENT |
             SEGMENT_USER |
             SEGMENT_CODE |
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
        ds = (. - gdt_start);
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
        cs32 = (. - gdt_start);
        QUAD(SEGMENT_4K |
             SEGMENT_DEFAULT_32BIT_OP |
             SEGMENT_PRESENT |
             SEGMENT_USER |
             SEGMENT_CODE |
             SEGMENT_ACCESSED |
             (0xF << (32 + 16)) | /* Segment Limit [19:16] */
             0xFFFF)              /* Segment Limit [15:0] */
    } > bios : descriptors

    /* 32-bit interrupt table */
    /* See Section 8.2 in AMD64 Architecture Programmer's Manual, Volume 2 for more details. */
    .idt ALIGN(8) : {
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
    } > bios : descriptors

    .gdt_desc ALIGN(8) : {
        SHORT(SIZEOF(.gdt) - 1)
        LONG(ADDR(.gdt))
    } > bios : descriptors

    .idt_desc ALIGN(8) : {
        SHORT(SIZEOF(.idt) - 1)
        LONG(ADDR(.idt))
    } > bios : descriptors

    gdt_desc_offset = ADDR(.gdt_desc) & 0xFFFF;
    idt_desc_offset = ADDR(.idt_desc) & 0xFFFF;

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
                                  + 4*12      /* AMD SEV metadata sections     |     */
                                  + 26        /* AMD SEV kernel hashes block   |     */
                                  + 22        /* AMD SEV metadata offset block |     */
                                  + 22        /* AMD SEV-ES reset block              */
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
        /* Kernel hashes location
         * https://github.com/tianocore/edk2/blob/f98662c5e35b6ab60f46ee4350fa0e6eab0497cf/OvmfPkg/ResetVector/X64/OvmfSevMetadata.asm#L88-L91
         * UEFI calculates this as
         * https://github.com/tianocore/edk2/blob/f98662c5e35b6ab60f46ee4350fa0e6eab0497cf/OvmfPkg/Include/Fdf/MemFd.fdf.inc#L86-L87
         */
        LONG(0x10000)
        /* This is calculated from the following:
         * https://github.com/tianocore/edk2/blob/0192f2d7cb3098d5cf1a2ed25874f47a08001de7/OvmfPkg/ResetVector/ResetVector.nasmb#L78
         * where those other values are set in the .fdf file here:
         * https://github.com/tianocore/edk2/blob/0192f2d7cb3098d5cf1a2ed25874f47a08001de7/OvmfPkg/AmdSev/AmdSevX64.fdf#L74-L78
         * Since both of them just add up to a single page (4096), we just calculate that directly.
         */
        LONG(0x1000)
        LONG(SEV_SECTION_KERNEL_HASHES)
        HIDDEN(sev_guided_structure_end = .);

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

        /* GUID calculated from
         * https://github.com/tianocore/edk2/blob/f98662c5e35b6ab60f46ee4350fa0e6eab0497cf/OvmfPkg/ResetVector/Ia16/ResetVectorVtf0.asm#L106-L114
         */
        HIDDEN(sev_kernel_fw_hash_block_start = .);
        /* SEV Hash GUID table. */
        LONG(0x10c00)
        /* This is the lower 1024 bits of the 4k page starting from the launch secrets page. */
        LONG(0x400)
        SHORT(sev_kernel_fw_hash_block_end - sev_kernel_fw_hash_block_start)
        LONG(0x7255371f)
        SHORT(0x3a3b)
        SHORT(0x4b04)
        SHORT(0x7b92)
        BYTE(0x1d) BYTE(0xa6) BYTE(0xef) BYTE(0xa8) BYTE(0xd4) BYTE(0x54)
        HIDDEN(sev_kernel_fw_hash_block_end = .);

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

        /* Footer: uint16 size, 16-byte GUID */
        SHORT(tables_end - tables_start)
        LONG(0x96b582de)
        SHORT(0x1fb2)
        SHORT(0x45f7)
        SHORT(0xeaba)
        BYTE(0xa3) BYTE(0x66) BYTE(0xc5) BYTE(0x5a) BYTE(0x08) BYTE(0x2d)
        HIDDEN(tables_end = .);
    } > bios : guid_tables

    ASSERT((. == TOP - 0x20), "GUID tables are to expected to end at top - 0x20")

    /* The reset vector needs to be placed 0x10 from the end of the file. */
    .reset_vector TOP - 0x10 : {
        *(.reset_vector)
        current = ABSOLUTE(.);
        FILL(0x00)
        . += TOP - current;
    } > bios : reset_vector
    ASSERT((. == TOP), "The reset vector must end at top")

    /DISCARD/ : {
        *(.eh_frame)
        *(.comment*)
    }
}
