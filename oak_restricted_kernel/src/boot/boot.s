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
.global _oak_start
.code64

_oak_start:
    # At this point we expect to have a valid page table identity mapping (at least) the lowest 1G
    # of physical memory; that means that the first PML4 entry must point to a valid PDP, and the
    # first entry of that PDP must point to a valid PD.
    # Our goal is to  map the first (physical) gigabyte to -2 GB in virtual address space; thus, we
    # need to make the last entry of the PML4 (covering the last 256T) point to a PDP, and the
    # second-to-last entry in that PDP point to the same PD as the PD in the lower half.
    #
    # We can reuse the existing data structures to achieve that goal. By pointing the last entry
    # of PML4 to the same PD as the first entry, and setting the second-to-last entry of that PD
    # to be the same as the first, we get our desired effect of mapping physical address 0x0 to
    # virtual address 0xFFFFFFFF80000000. As a side effect, this will map physical address 0x0 to
    # virtual address 0x0000007F80000000 (510*1G) as well, but that's fine. We'll be rewriting
    # the page tables soon after jumping to the kernel anyway.
    #
    # Note: don't touch %rsi, as that contains the address of the zero page.

    # Map the last entry of PML4 to the same location as the first.
    movq %cr3, %rbx        # rbx = cr3
    movq (%rbx), %rax      # rax = *rbx
    movq %rax, 4088(%rbx)  # rbx[511] = rax

    # Map the last entry of PDP to the same location as the first.
    # We're ignoring bit 51 (as that's commonly the encrypted bit).
    movabsq $0x0007FFFFFFFFF000, %rax  # rax = $const
    andq (%rbx), %rax                  # rax = *rbx & rax (mask out all but the address)
    movq (%rax), %rdx                  # rdx = *rax
    movq %rdx, 4080(%rax)              # rax[510] = rdx

    # Enable PGE (https://wiki.osdev.org/CPU_Registers_x86-64#CR4)
    movq %cr4, %rax
    orq $0b10000000, %rax
    movq %rax, %cr4

    # Finally, trigger a full TLB flush by overwriting CR3, even if it is the same value.
    movq %rbx, %cr3

    # Clear BSS: base address goes to RDI, value goes to AX, count goes into CX.
    mov $bss_start, %rdi
    mov $bss_size, %rcx
    xor %rax, %rax
    rep stosb

    mov $stack_start, %rsp
    # Push 8 bytes to fix stack alignment issue. Because we enter rust64_start with a jmp rather
    # than a call the function prologue means that the stack is no longer 16-byte aligned.
    push $0
    jmp rust64_start
