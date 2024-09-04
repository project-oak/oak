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

PHDRS
{
    /*
     * While lld (on Cargo's toolchain) will automatically create any phdrs referenced
     * using `.section { ...} :phdr` syntax, ld (on Bazel's toolchain) won't auto-create them,
     * so we declare them manually here.
     */
    setupdata PT_LOAD;
    boot PT_LOAD;
    text PT_LOAD;
    rodata PT_LOAD;
    data PT_LOAD;
    bss PT_LOAD;
}

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
         * We ignore most further fields since the relevant ones will be
         * populated by Stage 0.
         */
        . += 0x2E;
        /*
         * Set xloadflags to indicate that kernel/boot_params/cmdline/ramdisk
         * can be above 4G. This provides plenty of space for the VMM to load
         * an initial ramdisk.
         */
        SHORT(0x02)
        /*
         * We again ignore all subsequent fields since the relevant ones will be
         * populated by Stage 0.
         */
    } : setupdata

    /* Start of the kernel proper. */
    .boot ALIGN(4K) : {
        boot_start = .;
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

    .rela.dyn : {
        rela_start = .;
        *(.rela*)
        rela_end = .;
    } : rodata

    .data ALIGN(4K) : {
        data_start = .;
        *(.data .data.*)
        data_end = .;
    } : data

    .bss : ALIGN(4K) {
        *(.bss .bss.*)
    } : bss

    /* Stack grows down, so stack_start is the upper address in memory. */
    .stack (NOLOAD) : ALIGN(4K) {
        . += 32K;
    } : bss
    stack_start = .;

    /DISCARD/ : {
        *(.eh_frame*)
    }
}

