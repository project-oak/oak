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
    ram  PT_LOAD FLAGS(5);
}

SECTIONS {
    .boot 0x200000 : {
        ram_min = .;
        *(.boot)
    } : ram

    data_start = .;
    text_start = .;

    /*
     * The start point of execution is 0x200200, so ensure rust64_start is the
     * first symbol in the .text section.
     */
    .text : {
        KEEP(*(.text.rust64_start))
        *(.text .text.*)
    } : ram

    text_end = .;

    .rodata : {
        *(.rodata .rodata.*)
    } : ram

    .data : {
        *(.data .data.*)
    } : ram

    data_end = .;

    .bss : {
        bss_start = .;
        *(.bss .bss.*)
        bss_size = . - bss_start;
    }

    /* Stack grows down, so stack_start is the upper address in memory. */
    .stack (NOLOAD) : ALIGN(4K) {
        . += 512K;
    }
    stack_start = .;
}
