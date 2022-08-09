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
    text    PT_LOAD FLAGS(4 + 1); /* PF_R + PF_X */
    /* Read-only data. */
    rodata  PT_LOAD FLAGS(4); /* PF_R */
    /* Initialized read-write data. */
    data    PT_LOAD FLAGS(4 + 2); /* PF_R + PF_W */
    /* Uninitialized read-write data. */
    bss     PT_LOAD FLAGS(4 + 2); /* PF_R + PF_W */
    /* Special sections for SEV-SNP. */
    cpuid   PT_LOAD FLAGS(1 << 23);
    secrets PT_LOAD FLAGS(1 << 24);
}

SECTIONS {
    .boot 0x200000 : {
        ram_min = .;
        *(.boot)
    } : text

    data_start = .;
    text_start = .;

    .text : {
        *(.text .text.*)
    } : text

    text_end = .;

    .rodata : {
        *(.rodata .rodata.*)
    } : rodata

    .data : {
        *(.data .data.*)
    } : data

    data_end = .;

    .bss : {
        bss_start = .;
        *(.bss .bss.*)
        bss_size = . - bss_start;
    } : bss

    /* Stack grows down, so stack_start is the upper address in memory. */
    .stack (NOLOAD) : ALIGN(4K) {
        . += 512K;
    } : bss
    stack_start = .;

    .cpuid (NOLOAD) : ALIGN(2M) {
        . += 4K;
    } : cpuid

    .secrets (NOLOAD) : ALIGN(2M) {
        . += 4K;
    } : secrets
}
