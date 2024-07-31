.align 16
.section .tdx.bootstrap, "ax"
.code32

.global ap_start
ap_start:
    hlt

_park_ap:
    jmp _park_ap

.global _begin_of_tdx
_begin_of_tdx:
    cli

    test %esi, %esi
    jnz _park_ap

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

    # Skip BFV check
    # Skip UEFI SEC setup

    movl %cr4, %eax
    bts $0x05, %eax # PAE
    movl %eax, %cr4

    # page tables are set in the linker script
    movl $bios_pml4, %ecx
    movl %ecx, %cr3

    # In a TDX VM, IA32_EFER msr is set by tdx module.
    # No need for rdmsr/wrmsr

    # Protected mode + paging
    mov %cr0, %eax
    or $0x80000001, %eax # set PG
    mov %eax, %cr0

    # Reload CS, enter long mode, jump to 64-bit code.
    ljmpl $cs, $_tdx_64bit_start

.align 16
.code64
_tdx_64bit_start:
    # Clean up data segments.
    movw $ds, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %fs
    movw %ax, %gs
    movw %ax, %ss

    # We map the lower 640KiB using a TEMPMEM section. So no need to
    # accept memory page here.

    # Copy DATA from the ROM image (stored just after TEXT) to
    # the expected location. Source address goes to ESI, destination
    # goes to EDI, count goes to ECX.
    movl $text_end,   %esi
    movl $data_start, %edi
    movl $data_size,  %ecx
    rep movsd

    # Clear BSS: base address goes to EDI, value (0) goes to EAX,
    # count goes into ECX.
    movq $bss_start, %rdi
    movq $bss_size,  %rcx
    xorq %rax, %rax
    rep stosq

    # Set up the stack. Stack now is in ram_low
    movl $stack_start, %esp
    push $0

    movl $0xdeadbeaf, (TEST_DATA)

    # Set the first entry of PML4 to point to PDPT (0..512GiB).
    movl ${pdpt}, %esi
    orl $3, %esi              # esi |= 3 (PRESENT and WRITABLE)
    movl %esi, ({pml4})        # set first half of PML4[0]

    # Set the first entry of PDPT to point to PD_0 (0..1GiB).
    movl ${pd_0}, %esi
    orl $3, %esi              # esi |= 3 (PRESENT and WRITABLE)
    movl %esi, ({pdpt})        # set first half of PDPT[0]

    # Set the fourth entry of PDPT to point to PD_3 (3..4GiB).
    movl ${pdpt}, %eax
    movl ${pd_3}, %esi
    orl $3, %esi              # esi |= 3 (PRESENT and WRITABLE)
    movl %esi, 24(%eax)        # set first half of PDPT[3], each entry is 8 bytes

    # Set the first entry of PD_0 to point to and identity mapped huge page (0..2MiB).
    movl $0x83, %esi           # esi = 0x0 | 131 (PRESENT and WRITABLE and HUGE_PAGE)
    movl %esi, ({pd_0})        # set first half of PD_0[0]

    # Set the last entry of PD_3 to point to an identity-mapped 2MiB huge page ((4GiB-2MiB)..4GiB).
    # This is where the firmware ROM image is mapped, so we don't make it writable.
    movl ${pd_3}, %eax
    movl $0xFFE00000, %esi     # address of 4GiB-2MiB
    orl $0x81, %esi           # esi |= 129 (PRESENT and HUGE_PAGE)
    movl %esi, 0xFF8(%eax)     # set first half of PML4[511], each entry is 8 bytes

    # Reload PML4 to use the writable PML4
    xorq %rax, %rax
    movl ${pml4}, %eax
    movq %rax, %cr3

    # ...and jump to Rust code.
    jmp rust64_start
