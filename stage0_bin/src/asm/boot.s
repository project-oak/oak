.code16
.align 16
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
    jne 2f                # if not, skip ahead and crash
    mov (%esp), %ebx      # get the instruction pointer
    cmpw $0xa20f, (%ebx)  # was this really a CPUID instruction?
    jne 2f                # if not it might be injected by the hypervisor, skip ahead and crash
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
    mov %eax, %es         # needed for destination of stosb and movsb
    mov %eax, %ss

    # Set up a basic stack, as we may get interrupts.
    mov $stack_start, %esp

    # Determine if we're running under SEV.
    # Keep track of whether encryption is enabled in %ebp.
    mov $0xc0010131, %ecx     # SEV_STATUS MSR. See Section 15.34.10 in AMD64 Architecture Programmer's
                              # Manual, Volume 2 for more details.
    rdmsr                     # EDX:EAX <- MSR[ECX]
    push %edx                 # Store the raw result for future use on the stack.
    push %eax
    and $0b111, %eax          # eax &= 0b111;
                              # Bit 0 - SEV enabled
                              # Bit 1 - SEV-ES enabled
                              # Bit 2 - SEV-SNP active
    mov %eax, %ebp            # store the result in EBP for later use

    # See if we're under SEV-SNP, and if yes, pre-emptively PVALIDATE the first 640 KiB of memory,
    # as that's where we'll be storing many data structures.
    and $0b100, %eax          # eax &= 0b100; -- SEV-SNP active
    test %eax, %eax           # is eax zero?
    je 2f                     # if yes, no SNP, skip validation and jump ahead
    mov $0x0000, %ebx         # ebx = 0x0000 -- start address
    xor %ecx, %ecx            # ecx = 0 -- we're using 4K pages
    mov $0b1, %edx            # edx = 1 -- set RMP VALIDATED bit
    1:
    mov %ebx, %eax            # eax = ebx (PVALIDATE will clobber EAX)
    pvalidate                 # set validated bit in RMP, but ignore results for now
    movl (%ebx), %esi         # Read beginning...
    movl 4092(%ebx), %edi     # ...and end of page to invalidate cache. Read 4 bytes b/c 32-bit mode
    add $0x1000, %ebx         # ebx += 0x1000
    cmp $0xa0000, %ebx        # have we covered the full 640 KiB?
    jl 1b                     # if no, go back
    2:

    # Clear BSS: base address goes to EDI, value (0) goes to EAX, count goes into ECX.
    mov $bss_start, %edi
    mov $bss_size, %ecx
    xor %eax, %eax
    rep stosb

    mov $ap_bss_start, %edi
    mov $ap_bss_size, %ecx
    xor %eax, %eax
    rep stosb

    # now that BSS is set up, initialize the raw Rust variables
    pop %eax
    pop %edx
    mov %eax, (SEV_STATUS)     # Initialize the SEV_STATUS static variable in Rust.
    mov %edx, (SEV_STATUS+4)

    # Copy DATA from the ROM image (stored just after TEXT) to the expected location.
    # Source address goes to ESI, destination goes to EDI, count goes to ECX.
    mov $text_end, %esi
    mov $data_start, %edi
    mov $data_size, %ecx
    rep movsb

    # Copy AP bootstrap code to the expected location, similar to DATA above.
    mov $0xFFFFF000, %esi
    mov $ap_text_start, %edi
    mov $ap_text_size, %ecx
    rep movsb

    # Set the first entry of PML4 to point to PDPT (0..512GiB).
    mov ${pdpt}, %esi
    orl $3, %esi              # esi |= 3 (PRESENT and WRITABLE)
    mov %esi, ({pml4})        # set first half of PML4[0]

    # Set the first entry of PDPT to point to PD_0 (0..1GiB).
    mov ${pd_0}, %esi
    orl $3, %esi              # esi |= 3 (PRESENT and WRITABLE)
    mov %esi, ({pdpt})        # set first half of PDPT[0]

    # Set the fourth entry of PDPT to point to PD_3 (3..4GiB).
    mov ${pdpt}, %eax
    mov ${pd_3}, %esi
    orl $3, %esi              # esi |= 3 (PRESENT and WRITABLE)
    mov %esi, 24(%eax)        # set first half of PDPT[3], each entry is 8 bytes

    # Set the first entry of PD_0 to point to and identity mapped huge page (0..2MiB).
    mov $0x83, %esi           # esi = 0x0 | 131 (PRESENT and WRITABLE and HUGE_PAGE)
    mov %esi, ({pd_0})        # set first half of PD_0[0]

    # Set the last entry of PD_3 to point to an identity-mapped 2MiB huge page ((4GiB-2MiB)..4GiB).
    # This is where the firmware ROM image is mapped, so we don't make it writable.
    mov ${pd_3}, %eax
    mov $0xFFE00000, %esi     # address of 4GiB-2MiB
    orl $0x81, %esi           # esi |= 129 (PRESENT and HUGE_PAGE)
    mov %esi, 0xFF8(%eax)     # set first half of PML4[511], each entry is 8 bytes

    # Clear EDI, since we will use it later as the encrypted bit location to pass
    # into the 64-bit Rust entry point and by default we assume no encryption.
    xor %edi, %edi

    # Check whether encryption is enabled. The SEV status is stored in %ebp.
    test %ebp, %ebp           # is it zero?
    je no_encryption          # if yes, jump to no_encryption

    # Memory encryption enabled: set encrypted bits in the page tables.
    # First, determine the location of the C-bit in the page tables.
    # Keep track of which bit is the encrypted bit in EDI.
    mov $0x8000001F, %eax     # EAX = Fn8000_001F - Encrypted Memory Capabilities
    xor %ecx, %ecx            # ECX = 0 - we're not interested in a subpage
    cpuid                     # EAX, EBX, ECX, EDX = CPUID(EAX, ECX)
    and $0b111111, %ebx       # zero out all but EBX[5:0], which the C-bit location
    mov %ebx, %edi            # save the full C-bit location value for later to pass into the Rust
                              # entry point (RDI contains the first argument according to sysv ABI)
    cmp $32, %ebx             # is the C-bit less (or equal) to 32?
    jg 1f                     # if it's greater, proceed; otherwise, crash
    xor %edx, %edx            # EDX = 0x0
    mov $0x100, %eax          # EAX = 0x100 - Termination Request
    mov $0xC0010130, %ecx     # ECX = 0xC001_0130 -- GHCB MSR
    wrmsr                     # MSR[ECX] = EDX:EAX
    rep vmmcall               # VMGEXIT
    2:                        # If we're still alive, just go into a HLT loop.
    hlt
    jmp 2b
    1:                        # at this point we know the C-bit is > 32
    sub $32, %ebx             # we know the C-bit is > 32, so subtract that
    mov $1, %esi
    mov %ebx, %ecx
    shl %cl, %esi             # construct the encrypted bit mask, store it in ESI
    movl $0, (ENCRYPTED)      # ... and store it in the ENCRYPTED variable as well
    mov %esi, (ENCRYPTED+4)   # (lower half zeroed out as we expect it to be > 32, as above)

    # We set the encrypted bit for each of the leaf page table entries that we previously created.
    # For non-leaf entries, we don't bother setting the C-bit, as it's "don't care" (page walks are
    # always encrypted).
    # The encrypted bit is in the second half of each 8-byte entry, so we add an extra offset of 4 bytes.
    mov ${pd_0}, %eax
    mov %esi, 4(%eax)         # set second half of PD_0[0]
    mov ${pd_3}, %eax
    mov %esi, 0xFFC(%eax)     # set second half of PD_3[511], each entry is 8 bytes
no_encryption:

    # Load PML4
    mov ${pml4}, %eax
    mov %eax, %cr3

    # PAE
    mov $0b100000, %eax
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
    
    # ...and jump to Rust code.
    jmp rust64_start
