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
    /* The Restricted Kernel is Loaded between 2MiB and 11MiB, so we
     * load this wrapper at 16Mib for now. This will go away once the
     * wrapper and the Restricted Kernel supports relocation.
     */
    . = 16M;

    /* 64-bit Entrypoint for the wrapper. */
    .boot : ALIGN(4K) {
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

