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
HIDDEN(BIOS_SIZE = 256K);

MEMORY {
    bios : ORIGIN = TOP - BIOS_SIZE, LENGTH = BIOS_SIZE
}

ENTRY(reset_vector)

/* Segment descriptor flags.
 * See Section 4.8 in AMD64 Architecture Programmer's Manual, Volume 2 for more details.
 */
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

    pml4_offset = ADDR(.rodata.pml4);

    .rodata.pdpt ALIGN(4K) : {
        QUAD(ADDR(.rodata.pd) | PAGE_PRESENT | PAGE_WRITABLE) /* 0..1 GiB */
        QUAD(0)
        QUAD(0)
        QUAD(ADDR(.rodata.pd) | PAGE_PRESENT | PAGE_WRITABLE) /* 3..4 GiB */
    } > bios

    .rodata.pd ALIGN(4K) : {
        QUAD(0 | PAGE_PRESENT | PAGE_WRITABLE | PAGE_SIZE) /* 0 .. 2 MiB */
        FILL(0x00)
        . += 510 * 8;
        QUAD((TOP - 2M) | PAGE_PRESENT | PAGE_WRITABLE | PAGE_SIZE) /* (4GiB - 2MiB) .. 4 GiB */
    } > bios

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
        . += 4K;
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
         * Although according to the manual in 64-bit mode WRITABLE should be ignored, at least qemu
         * will cause a #GP if we try to load SS with a segment descriptor that doesn't have it set.
         */
        ds = . - ADDR(.rodata.gdt);
        QUAD(SEGMENT_PRESENT | SEGMENT_USER | SEGMENT_WRITABLE)
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
