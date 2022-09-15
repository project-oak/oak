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
HIDDEN(BIOS_SIZE = 512K);

MEMORY {
    bios : ORIGIN = TOP - BIOS_SIZE, LENGTH = BIOS_SIZE
}

ENTRY(reset_vector)

/* Segment descriptor flags.
 * See Sections 4.7 and  4.8 in AMD64 Architecture Programmer's Manual, Volume 2 for more details.
 */
HIDDEN(SEGMENT_4K = 1 << (32 + 23)); /* G */
HIDDEN(SEGMENT_DEFAULT_32BIT_OP = 1 << (32 + 22)); /* D/B */
HIDDEN(SEGMENT_LONG = 1 << (32 + 21));
HIDDEN(SEGMENT_PRESENT = 1 << (32 + 15)); /* P */
HIDDEN(SEGMENT_USER = 1 << (32 + 12)); /* S */
HIDDEN(SEGMENT_CODE = 1 << (32 + 11));
HIDDEN(SEGMENT_WRITABLE = 1 << (32 + 9));
HIDDEN(SEGMENT_CONFORMING = 1 << (32 + 10));

/* Page table flags */
HIDDEN(PAGE_PRESENT = 1 << 0);
HIDDEN(PAGE_WRITABLE = 1 << 1);
HIDDEN(PAGE_SIZE = 1 << 7);

SECTIONS {
    . = ORIGIN(bios);

    .rodata.pml4 ALIGN(4K) : {
        QUAD(ADDR(.rodata.pdpt) | PAGE_PRESENT | PAGE_WRITABLE) /* 0..512 GiB */
    } > bios

    pml4_addr = ADDR(.rodata.pml4);

    .rodata.pdpt ALIGN(4K) : {
        QUAD(ADDR(.rodata.pd) | PAGE_PRESENT | PAGE_WRITABLE) /* 0..1 GiB */
        QUAD(0)
        QUAD(0)
        QUAD(ADDR(.rodata.pd) | PAGE_PRESENT | PAGE_WRITABLE) /* 3..4 GiB */
    } > bios

    pdpt_addr = ADDR(.rodata.pdpt);

    .rodata.pd ALIGN(4K) : {
        QUAD(0 | PAGE_PRESENT | PAGE_WRITABLE | PAGE_SIZE) /* 0 .. 2 MiB */
        FILL(0x00)
        . += 510 * 8;
        QUAD((TOP - 2M) | PAGE_PRESENT | PAGE_WRITABLE | PAGE_SIZE) /* (4GiB - 2MiB) .. 4 GiB */
    } > bios

    pd_addr = ADDR(.rodata.pd);

    .rodata : {
        KEEP(*(.rodata .rodata.*))
    } > bios

    .text : {
        *(.text .text.*)
    } > bios

    .data : {
        *(.data .data.*)
    } > bios

    .bss :  {
        bss_start = .;
        *(.bss .bss.*)
        bss_size = . - bss_start;
    } > bios

    .stack ALIGN(4K) (NOLOAD) : {
        . += 16K;
        stack_start = .;
    } > bios

    /* Everything below this line interacts with 16-bit code, so should be kept as close to the end of the file as
     * possible; max TOP - 32k. */

    .text16 TOP - 1K : {
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
        QUAD(SEGMENT_LONG | SEGMENT_PRESENT | SEGMENT_USER | SEGMENT_CODE)
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
             (0xF << (32 + 16)) | /* Segment Limit [19:16] */
             0xFFFF); /* Segment Limit [15:0] */
    } > bios

    .rodata.idt ALIGN(8) : {
        QUAD(0)
    } > bios
    
    .rodata.gdt_desc ALIGN(8) : {
        SHORT(SIZEOF(.rodata.gdt) - 1)
        LONG(ADDR(.rodata.gdt))
    } > bios

    .rodata.idt_desc ALIGN(8) : {
        SHORT(0)
        LONG(ADDR(.rodata.idt))
    } > bios

    gdt_desc_offset = ADDR(.rodata.gdt_desc) & 0xFFFF;
    idt_desc_offset = ADDR(.rodata.idt_desc) & 0xFFFF;

    /* GUIDed tables have to *end* at 0x20 from the end of the file.
     * Documentation about the GUID table format can be found in QEMU docs:
     * https://github.com/qemu/qemu/blob/master/docs/specs/sev-guest-firmware.rst
     * and EDK2 source code:
     * https://github.com/tianocore/edk2/blob/master/OvmfPkg/ResetVector/Ia16/ResetVectorVtf0.asm
     */
    .guid_tables TOP - 0x20 - 0x28 : {
        HIDDEN(tables_start = .);
        /* SEV-ES reset block: uint32 addr, uint16 size, 16-byte GUID */
        HIDDEN(sev_es_reset_block_start = .);
        LONG(0xDEADBEEF) /* Placeholder values */
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
        FILL(0x00)
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
