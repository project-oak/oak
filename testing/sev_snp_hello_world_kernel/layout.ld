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

ENTRY(_start)

PHDRS
{
    /* Note that the permissions flags are currently not respected. */
    /* Keep the sections here sorted from lowest memory address to largest; crosvm
     * has a sanity check that expects the section with the lowest address to come
     * first.
     */
    /* Executable text. */
    boot    PT_LOAD FLAGS(4 + 1); /* PF_R + PF_X */
    text    PT_LOAD FLAGS(4 + 1); /* PF_R + PF_X */
    /* Read-only data. */
    rodata  PT_LOAD FLAGS(4); /* PF_R */
    /* Initialized read-write data. */
    data    PT_LOAD FLAGS(4 + 2); /* PF_R + PF_W */
    /* Uninitialized read-write data. */
    bss     PT_LOAD FLAGS(4 + 2); /* PF_R + PF_W */
}

/* To set kernel VMA to high memory, set this to 0xFFFFFFFF80000000. */
KERNEL_MEM_START = 0x0;

SECTIONS {
    /*
     * Boot code is executed with identity mapping; the main duty of the boot
     * code is to set up proper page tables before jumping to the kernel proper.
     * We place that at 2M (both virtual and physical)
     */
    .boot 0x200000 : {
        ram_min = .;
        *(.boot)
    } : boot

    /*
     * Load the rest of the kernel after KERNEL_MEM_START. The idea is that the initial
     * boot code should set map KERNEL_MEM_START to physical address 0; therefore, all
     * VMAs will be LMA + KERNEL_MEM_START.
     */
    . += KERNEL_MEM_START;

    data_start = .;
    text_start = .;

    .text ALIGN(2M) : AT(ADDR(.text) - KERNEL_MEM_START) {
        *(.text .text.*)
    } : text

    text_end = .;

    .rodata ALIGN(2M) : {
        *(.rodata .rodata.*)
    } : rodata

    .data ALIGN(2M) : {
        *(.data .data.*)
    } : data

    data_end = .;

    .bss : ALIGN(2M) {
        bss_start = .;
        *(.bss .bss.*)
        bss_size = . - bss_start;
    } : bss

    .ghcb (NOLOAD) : ALIGN(2M) {
    } : bss
    ASSERT((SIZEOF(.ghcb) == 0x1000), "GHCB page needs to be exactly 4K in size")

    /* Stack grows down, so stack_start is the upper address in memory. */
    .stack (NOLOAD) : ALIGN(2M) {
        . += 512K;
    } : bss
    stack_start = .;

    /DISCARD/ : {
        *(.eh_frame*)
    }
}
