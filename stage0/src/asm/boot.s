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
    add $2, %eax          # increment it by 2 (size of the CPUID instruction)
    push %eax             # push it back on stack for iret
    xor %eax, %eax        # zero out RAX
    xor %edx, %edx        # zero out RDX
    iret                  # go back
    2:                    # this wasn't because RDMSR
    int $8                # trigger a double fault and crash

_protected_mode_start:
    # Switch to a flat 32-bit data segment, giving us access to all 4G of memory.
    mov $ds, %eax
    mov %eax, %ds
    mov %eax, %ss

    # Set up a basic stack, as we may get interrupts.
    mov $stack_start, %esp

    # Determine if we're running under SEV. Keep track of which bit is the encrypted bit in %rsi.
    mov $0, %esi              # by default, no encryption
    mov $0xc0010131, %ecx     # SEV_STATUS MSR. See Section 15.34.10 in AMD64 Architecture Programmer's
                              # Manual, Volume 2 for more details.
    rdmsr                     # EDX:EAX <- MSR[ECX]
    and $3, %eax              # eax &= 0b11;
                              # Bit 0 - SEV enabled
                              # Bit 1 - SEV-ES enabled
    test %eax, %eax           # is it zero?
    je no_encryption          # if yes, jump to no_encryption

    # Memory encryption enabled: set encrypted bits in the page tables.
    # We assume the encrypted bit is bit 51, for now.
    mov $51, %esi
    mov $pml4_addr, %eax
    orl $0x80000, 4(%eax)     # PML4[0] |= (1 << 51)
    mov $pdpt_addr, %eax
    orl $0x80000, 4(%eax)     # PDPT[0] |= (1 << 51)
    orl $0x80000, 4092(%eax)  # PDPT[511] |= (1 << 51)
    mov $pd_addr, %eax
    orl $0x80000, 4(%eax)     # PD[0] |= (1 << 51)
    orl $0x80000, 4092(%eax)  # PD[511] |= (1 << 51)
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
