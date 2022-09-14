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

    # Determine if we're running under SEV
    mov $0xc0010131, %ecx     # SEV_STATUS MSR
    rdmsr                     # EDX:EAX <- MSR[ECX]
    and $3, %eax              # eax &= 0b11;
    test %eax, %eax           # is it zero?
    je no_encryption          # if yes, jump to no_encryption
    # Memory encryption enabled: set encrypted bits in the page tables.

    # Load a flat 32-bit DS by jumping through protected mode.
    mov %cr0, %eax
    or $1, %al
    mov %eax, %cr0
    mov $ds, %bx
    mov %bx, %ds
    or $0xFE, %al
    mov %eax, %cr0

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

    # ...and jump to Rust code.
    jmp rust64_start
