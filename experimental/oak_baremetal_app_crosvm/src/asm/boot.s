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

.section .boot, "ax"
.global _start
.code64

_start:
    # We need to map virtual 0xFFFFFFFF80000000 to physical 0:
    # sign extension  |   PML4    |    PDP    |    PD     |         page
    # 6             4 | 4       4 | 3       3 | 3       2 | 2                    0
    # 321098765432109 | 876543210 | 987654321 | 098765432 | 1098765432109876543210
    # ----------------+-----------+-----------+-----------+-----------------------
    # 111111111111111 | 111111111 | 111111111 | 000000000 | 0000000000000000000000
    # As the VMM is supposed to set up identity mapping for the lowest 1G of
    # memory, we can just piggyback on the existing data structures by:
    # a) setting the last PML4 entry to point to the same PDP entry as the first
    # b) setting the last PDP entry to point ot the same PD entry as the first.
    # That should be enough to get the kernel virtual addresses to the right place,
    # as the PD should be set up for mapping to low physical addresses. This will
    # create another mapped region at 0xFF80000000, but that's fine as we won't use
    # it.
    # Note: don't touch %rsi, as that contains the address of the zero page.

    # Map the last entry of PML4 to the same location as the first.
    movq %cr3, %rbx        # rbx = cr3
    movq (%rbx), %rax      # rax = *rbx
    movq %rax, 4088(%rbx)  # rbx[511] = rax
    invlpg (%rbx)

    # Map the last entry of PDP to the same location as the first.
    #  0x000FFFFFFFFFF000
    movabsq $0x000FFFFFFFFFF000, %rax  # rax = $const (mask out other fields but the address)
    andq (%rbx), %rax                # rax = *rbx & rax
    movq (%rax), %rdx                # rdx = *rax
    movq %rdx, 4088(%rax)            # rax[511] = rdx
    invlpg (%rax)
 
    # Invalidate the page cache.
    invlpg 0xFFFFFFFF80000000

    mov $stack_start, %rsp
    # Push 8 bytes to fix stack alignment issue. Because we enter rust64_start
    # with a jmp rather than a call the function prologue means that the stack
    # is no loger 16-byte aligned.
    push $0
    jmp rust64_start
