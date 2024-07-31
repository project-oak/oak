.align 16
.section .tdx.bootstrap, "ax"
.code32

.global ap_start

ap_start:
    hlt

# Translated from TD-shim's reset vector
# https://github.com/confidential-containers/td-shim/blob/a7ab6cc310dcf9af0b20895a11898bb53ac156dd/td-shim/ResetVector/Ia32/ReloadFlat32.asm#L18

# Input: RAX/EAX, RFLAGS, RCX, RDX, RBX, RSI, RDI, RBP, R8
# But the first goal is just boot into 64-bit mode. So we don't preserve them.
.global _begin_of_tdx
_begin_of_tdx:
    cli

    # ReloadFlat32
    # Set up descriptors
    movl $gdt_desc_offset, %ebx
    lgdtl (%ebx)

    movl $0x00000023, %eax # SEC_DEFAULT_CR0
    movl %eax, %cr0

    ljmpl $cs32, $_tdx_32bit_long_mode_start

_tdx_32bit_long_mode_start:

    movl $0x640, %eax # SEC_DEFAULT_CR4
    movl %eax, %cr4

    movl $ds, %eax
    movl %eax, %ds
    movl %eax, %es
    movl %eax, %fs
    movl %eax, %gs
    movl %eax, %ss

    # ReloadFlat32 complete
    # Skip BFV check
    # Skip UEFI SEC setup

    # Transition32FlatTo64Flat
    movl %cr4, %eax
    bts $0x05, %eax
    movl %eax, %cr4

    # esp [6:0] holds gpaw. if it is at least 52 bits, we need
    # to set LA57 and use 5-level paging
    # Skipped the esp check because currently the platform has
    # c-bit at the 51 bit. 4-level paging is enough.

    mov $stack_start, %esp

_temp_loop_start:
    jmp _temp_loop_start # infinite loop debugging

    # Before setting up page tables, we need to accept the lower 640KB
    # memory. pdpt is at 0x8000; pml4 is at 0x7000, pd_0 is at 0x9000;
    # pd_3 is at 0xa000

    # Set the first entry of PML4 to point to PDPT (0..512GiB).
    movl ${pdpt}, %esi
    orl $3, %esi              # esi |= 3 (PRESENT and WRITABLE)

    movl %esi, ({pml4})        # set first half of PML4[0] # CRASH HERE

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
    orl $0x83, %esi           # esi |= 129 (PRESENT and HUGE_PAGE)
    mov %esi, 0xFF8(%eax)     # set first half of PML4[511], each entry is 8 bytes

    # Load PML4
    mov ${pml4}, %eax
    mov %eax, %cr3

    # In a TDX VM, IA32_EFER msr is set by tdx module. 

    # Protected mode + paging
    mov %cr0, %eax
    or $0x80000001, %eax
    mov %eax, %cr0

    # Reload CS, enter long mode, jump to 64-bit code.
    ljmpl $cs, $_tdx_64bit_start

.align 16
.code64
_tdx_64bit_start:
    # Transition32FlatTo64Flat complete
    #jmp _tdx_64bit_start # infinite loop debugging

    mov $0x00000000ffffffff, %rax
    andq %rax, %rsi
    andq %rax, %rbp
    andq %rax, %rsp

    xor %rax, %rax # TDG.VP.VMCALL leaf function
    xor %rcx, %rcx # 0xfc00, TDVMCALL_EXPOSE_REGS_MASK
    xor %r10, %r10
    mov $1, %rdx   # use r11
    mov $30, %r11  # INSTRUCTION.io
    mov $4, %r12  # size, 4=4bytes
    mov $1, %r13   # 1 = write
    mov $0x3f8, %r14 # port number
    mov $0x46414542, %r15  # 'BEAF'
    .byte 0x66, 0x0f, 0x01, 0xcc # tdcall

    # Set up the stack.
    mov $stack_start, %esp
    #push $0

    nop
    nop
    nop

    hlt
