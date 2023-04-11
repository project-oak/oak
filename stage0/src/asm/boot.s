.code16
.section .text16, "ax"
.global _start
_start :
    # Enter long mode. This code is inspired by the approach shown at
    # https://wiki.osdev.org/Entering_Long_Mode_Directly
    cli

    xor %eax, %eax
    mov %eax, %cr3

    # Set up descriptors
    mov $gdt_desc_offset, %si
    lgdtl %cs:(%si)
    mov $idt_desc_offset, %si
    lidtl %cs:(%si)

    # Enter protected mode, but don't enable paging.
    mov %cr0, %eax
    or $1, %eax
    mov %eax, %cr0
    ljmpl $cs32, $_protected_mode_start

.align 16
.code32
.global gp_handler
gp_handler:
    pop %eax              # ignore the error code for now
    pop %eax              # pop the return address
    cmpw $0x320F, (%eax)  # are we trying to execute RDMSR?
    jne 2f                # if not, skip ahead
    add $2, %eax          # increment it by 2 (size of the RDMSR instruction)
    push %eax             # push it back on stack for iret
    xor %eax, %eax        # zero out RAX
    xor %edx, %edx        # zero out RDX
    iret                  # go back
    2:                    # this wasn't because RDMSR
    int $8                # trigger a double fault and crash
.global vc_handler
# Really limited #VC handler that only knows how to fill in EBX in case of CPUID.
# As CPUID can alter EAX, EBX, ECX and EDX we zero out the other three registers.
vc_handler:
    pop %ebx              # get the error code
    cmp $0x72, %ebx       # is this about CPUID?
    jne 2f                # if not, skip ahead
    cmp $0x0, %ecx        # are we asked for a CPUID subleaf?
    jne 2f                # if yes, skip ahead, as we don't support subleaves
    # Use the GHCB MSR protocol to request one page of CPUID information. The protocol itself is
    # described in Section 2.3.1 of SEV-ES Guest-Hypervisor Communication Block Standardization spec.
    mov %eax, %edx        # EDX = EAX (move the CPUID function number to GHCBData[63:32])
    mov $0x40000004, %eax # EAX = Request EBX (0b01 << 30) | CPUID Request (0x004)
    mov $0xC0010130, %ecx # ECX = 0xC001_0130 -- GHCB MSR
    wrmsr                 # MSR[ECX] = EDX:EAX
    rep vmmcall           # VMGEXIT
    rdmsr                 # EDX:EAX = MSR[ECX]
    cmp $0x40000005, %eax # EAX should contain EBX data (0b01 << 30) | CPUID Response (0x005)
    jne 2f                # if not, crash
    addl $2, (%esp)       # move return address forward past the CPUID instruction
    xor %eax, %eax        # EAX = 0
    mov %edx, %ebx        # EBX = EDX (that's where the cpuid value is)
    xor %ecx, %ecx        # ECX = 0
    xor %edx, %edx        # EDX = 0
    iret                  # go back
    2:                    # this wasn't because CPUID or the response wasn't what we expected
    int $8                # trigger double fault and crash

_protected_mode_start:
    # Switch to a flat 32-bit data segment, giving us access to all 4G of memory.
    mov $ds, %eax
    mov %eax, %ds
    mov %eax, %ss

    # Set up a basic stack, as we may get interrupts.
    mov $stack_start, %esp

    # Set up the 4K page table for the lowest 2 MiB of memory. We set up an individual page table
    # instead of using a 2MiB hugepage because we may need to change the encrypted bit and the
    # RMP state on individual 4K pages.
    mov $pt_addr, %ecx      # base for page table
    mov $1, %eax            # loop counter: we start at 1 so that 0 (the first 4K) would remain
                            # unmapped (so that null pointers would trigger a page fault)
    1:
    mov %eax, %edx          # edx = eax
    sal $12, %edx           # edx = edx << 12 (2^12 == 4K)
    orl $3, %edx            # edx |= 3 (PRESENT and WRITABLE)
    mov %edx, (%ecx,%eax,8) # PT[eax] = edx (memory address is ecx+8*eax)
    inc %eax                # eax = eax + 1
    cmp $512, %eax          # are we done with all 512 entries?
    jne 1b                  # no, we were not

    # Determine if we're running under SEV. Keep track of which bit is the encrypted bit in %rsi.
    mov $0, %esi              # by default, no encryption
    mov $0xc0010131, %ecx     # SEV_STATUS MSR. See Section 15.34.10 in AMD64 Architecture Programmer's
                              # Manual, Volume 2 for more details.
    rdmsr                     # EDX:EAX <- MSR[ECX]
    and $0b111, %eax          # eax &= 0b111;
                              # Bit 0 - SEV enabled
                              # Bit 1 - SEV-ES enabled
                              # Bit 2 - SEV-SNP active
    test %eax, %eax           # is it zero?
    je no_encryption          # if yes, jump to no_encryption
    # See if we're under SEV-SNP, and if yes, pre-emptively PVALIDATE the first megabyte of memory, as that's
    # where we'll be storing many data structures.
    and $0b100, %eax          # eax &= 0b100; -- SEV-SNP active
    test %eax, %eax           # is eax zero?
    je 2f                     # if yes, no SNP, skip validation and jump ahead
    mov $0x1000, %ebx         # ebx = 0x1000 -- start address (skipping first page as that's not mapped)
    xor %ecx, %ecx            # ecx = 0 -- we're using 4K pages
    mov $0b1, %edx            # edx = 1 -- set RMP VALIDATED bit
    1:
    mov %ebx, %eax            # eax = ebx (PVALIDATE will clobber EAX)
    pvalidate                 # set validated bit in RMP, but ignore results for now
    add $0x1000, %ebx         # ebx += 0x1000
    cmp $0x100000, %ebx       # have we covered the full megabyte?
    jl 1b                     # if no, go back
    2:

    # Memory encryption enabled: set encrypted bits in the page tables.
    # First, determine the location of the C-bit in the page tables.
    mov $0x8000001F, %eax     # EAX = Fn8000_001F - Encrypted Memory Capabilities
    xor %ecx, %ecx            # ECX = 0 - we're not interested in a subpage
    cpuid                     # EAX, EBX, ECX, EDX = CPUID(EAX, ECX)
    and $0b111111, %ebx       # zero out all but EBX[5:0], which the C-bit location
    push %ebx                 # save the full C-bit location value for later
    sub $32, %ebx             # let's assume the encrypted bit is > 32, as it simplifies logic below
    mov $1, %edi
    mov %ebx, %ecx
    shl %cl, %edi             # construct the bit mask for the loop, store it in EDI

    # Note that this sets the encrypted bit for _all_ entries in the page tables, even
    # if they are unused. This is fine, as those entries will still not have the PRESENT
    # bit set and thus will be ignored by the CPU.
    mov $pml4_addr, %eax      # Base values for all page tables.
    mov $pdpt_addr, %ebx
    mov $pd_addr, %ecx
    mov $pt_addr, %edx
    xor %esi, %esi            # zero out esi for use as the loop counter
    1:
    # Page tables are 8 bytes, so these offsets boil down to base + (ESI * 8) + 4
    or %edi, 4(%eax,%esi,8)   # PML4[ESI] |= EDI
    or %edi, 4(%ebx,%esi,8)   # PDPT[ESI] |= EDI
    or %edi, 4(%ecx,%esi,8)   # PD[ESI] |= EDI
    or %edi, 4(%edx,%esi,8)   # PT[ESI] |= EDI
    inc %esi                  # ESI = ESI + 1
    cmp $512, %esi            # have we changed all 512 entries?
    jne 1b                    # ESI < 512, go back to square 1
    pop %esi                  # keep track of the encrypted bit for main
no_encryption:

    # Load PML4
    mov $pml4_addr, %eax
    mov %eax, %cr3

    # PAE + PGE
    mov $0b10100000, %eax
    mov %eax, %cr4

    # Read EFER, enable LME
    mov $0xC0000080, %ecx
    rdmsr
    or $0x00000100, %eax
    wrmsr

    # Protected mode + paging
    mov %cr0, %eax
    or $0x80000001, %eax
    mov %eax, %cr0

    # Reload CS, enter long mode, jump to 64-bit code.
    ljmpl $cs, $_long_mode_start

.align 16
.code64
_long_mode_start:
    # Clean up data segments.
    movw $ds, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %fs
    movw %ax, %gs
    movw %ax, %ss

    # Set up the stack.
    mov $stack_start, %esp
    push $0

    # Clear BSS: base address goes to RDI, value goes to AX, count goes into CX.
    mov $bss_start, %edi
    mov $bss_size, %ecx
    xor %rax, %rax
    rep stosb
    
    # ESI should contain the encrypted bit number. Move it to EDI, as that's the first argument
    # according to sysv ABI.
    mov %esi, %edi

    # ...and jump to Rust code.
    jmp rust64_start
