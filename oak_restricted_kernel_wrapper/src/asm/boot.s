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

.section .boot, "ax"
.global _wrapper_entry
.code64

_wrapper_entry:
    # At this point we expect to have a valid page table identity mapping (at least) the lowest 1G
    # of physical memory.
    #
    # Note: don't touch %rsi, as that contains the address of the zero page.

    # Set up the new stack.
    mov $stack_start, %rsp
    # Push 8 bytes to fix stack alignment issue. Because we enter rust64_start with a jmp rather
    # than a call the function prologue means that the stack is no longer 16-byte aligned.
    push $0
    jmp rust64_start
