/*
 * Copyright 2023 The Project Oak Authors
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

ENTRY(_wrapper_entry)

SECTIONS {
    /* 
     * The setup-data for the kernel. In the Linux kernel this also includes
     * the real-mode code, which we don't support. 
     *
     * This section will be split off by the hypervisor and loaded separately.
     * It acts as the initial values for the setup_data field in the boot
     * parameters. We can mostly leave it 0 for the restricted kernel, as long
     * as it looks similar enough to a Linux bzImage so that the VMM will
     * recognize it.
     */
    . = 32M - 4K;
    .setupdata ALIGN(4K) : {
        FILL(0x00)
        /* Padding until the setup struct starts. */
        . += 0x1F1;
        /* Number of 512B sectors -1. Setup section is 4KiB. */ 
        BYTE(0x07)
        /* Padding for ignored fields. */
        . += 0xC;
        /* Magic number (0xAA55) */
        SHORT(0xAA55)
        /* Jump instruction. */
        BYTE(0xEB)
        /*
         * Relative offset for the jump instruction, which can be used to
         * determine the size of the header (Header ends at 0x202 + 0x6A).
         */
        BYTE(0x6A)
        /* Magic number (HdrS) */
        LONG(0x53726448)
        /* Boot protocol version (2.15) */
        SHORT(0x020F)
        /*
          * We ignore all further fields since the relevant ones will be
          * populated by Stage 0.
          */
    } : setupdata
    /* The Restricted Kernel is Loaded between 2MiB and 17MiB, so we
     * load this wrapper at 32Mib for now. This will go away once the
     * wrapper and the Restricted Kernel supports relocation.
     */
    . = 32M;

    /* Start of the kernel proper. */
    .boot ALIGN(4K) : {
        FILL(0x00)
        /* The 64-bit entry point must be at offset 0x200 from the start of
         * kernel.
         */
        . += 0x200;
        *(.boot)
    } : boot

    .text ALIGN(4K) : {
        *(.text .text.*)
    } : text

    .rodata ALIGN(4K) : {
        *(.rodata .rodata.*)
    } : rodata

    .data ALIGN(4K) : {
        *(.data .data.*)
    } : data

    .bss : ALIGN(4K) {
        *(.bss .bss.*)
    } : bss

    /* Stack grows down, so stack_start is the upper address in memory. */
    .stack (NOLOAD) : ALIGN(4K) {
        . += 512K;
    } : bss
    stack_start = .;

    /DISCARD/ : {
        *(.eh_frame*)
    }
}

