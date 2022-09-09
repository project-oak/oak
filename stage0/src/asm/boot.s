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

    # Load PML4
    mov $pml4_offset, %eax
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
