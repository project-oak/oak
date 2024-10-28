.align 16
.section .tdx.bootstrap, "ax"
.code32

.global ap_start
ap_start:
    hlt

.global _begin_of_tdx
_begin_of_tdx:
    # VCPU_INDEX is in esi
    cli

    andl $0x3f, %ebx # [6:0] GPAW
    movl %ebx, %ebp

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

    # Note that no matter what the GPAW is, we only use 4-level
    # paging in stage0. Linux will set up its own PTs later.
    movl %cr4, %eax
    bts $0x05, %eax # PAE
    movl %eax, %cr4

    # page tables are set in the linker script
    movl $bios_pml4, %ecx
    movl %ecx, %cr3

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

    # Park the APs
    test %esi, %esi
    jnz _park_ap_64bit

    # BSP re-creates a set of page table in ram_low
    # Clear BSS: base address goes to EDI, value (0) goes to EAX,
    # count goes into ECX. Page tables will be located in BSS
    movl $bss_start, %edi
    movl $bss_size,  %ecx
    xorl %eax, %eax
    rep stosb

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
    movq ${pml4}, %rax
    movq %rax, %cr3

    # Copy DATA from the ROM image (stored just after TEXT) to
    # the expected location. Source address goes to ESI, destination
    # goes to EDI, count goes to ECX.
    movl $text_end,   %esi
    movl $data_start, %edi
    movl $data_size,  %ecx
    rep movsd

    # Set up the stack. Stack now is in ram_low
    movl $stack_start, %esp
    push $0

    # Set GPAW
    movl %ebp, (GPAW)

    # ...and jump to Rust code.
    jmp rust64_start

_park_ap_64bit:
    leaq (AP_IN_64BIT_COUNT), %rcx       # Load address of AP_IN_64BIT_COUNT onto rcx
    lock incq (%rcx)                     # Atomically increment AP_IN_64BIT_COUNT

    movl %esi, %ebp                      # esi has the VCPU_INDEX, save it in ebp

# APs poll the firmware mailbox, where the BSP will set the address
# of the OS mailbox. The firmware mailbox is located at symbol TD_MAILBOX_START
# (see layout.ld). On startup, that address (and its entire page) is all zeros.
# We use the following simple structure for the firmware mailbox:
#
#  Field                Length(bytes)     Description
#  -----------------------------------------------
#  IsAddressSet         8                 0 if OS mailbox address is unset, any other value otherwise. Aligning to 8 bytes.
#  OsMailboxAddress     8                 Physical address of OS mailbox.
#
_ap_poll_firmware_mailbox:
    # By the time APs reach this loop, they are using the hard-coded page
    # tables from ROM (BIOS area, [4GiB - 2MiB, 4Gib), i.e. the top 2MiB of the memory).

    pause                               # Allow power saving while waiting,

    movq TD_MAILBOX_START, %rax         # Copy value at TD_MAILBOX_START (field IsAddressSet) into rax.
    testq %rax, %rax                    # If IsAddressSet
    jz _ap_poll_firmware_mailbox        # equals 0, it means OsMailboxAddress not set, loop.

    movq (TD_MAILBOX_START + 8), %rdx   # Otherwise, save OsMailboxAddress value in rdx
    # Proceed to _ap_poll_os_mailbox


.equ WakeupCommand,  0x0001

# APs poll the OS mailbox, where the OS will send them commands.
# The structure is defined in stage0/src/mailbox.rs
# INPUTS expected:
#   - OsMailboxAddress in rdx register.
#   - CPU_ID of current AP in ebp register.
_ap_poll_os_mailbox:
    pause                               # Allow power saving while waiting.

    # The apic_id field (4 bytes at offset 4) is ID of the CPU for which this command is for.
    cmpl 4(%rdx), %ebp                  # If apic_id not equals my CPU_ID (ebp),
    jne _ap_poll_os_mailbox             # then loop.

    # First 2 bytes of OS mailbox contain the field `command`. We only recognise WakeupCommand.
    cmpw $WakeupCommand, (%rdx)         # If command not equals WakeupCommand,
    jne _ap_poll_os_mailbox             # then loop.

    # Wakeup, go to OS-provided address at field wakeup_vector (8 bytes at offset 8)
    movq 8(%rdx), %rax                  # Save value of wakeup_vector to rax.
    movw $0, (%rdx)                     # Write 0 to command field to acknowledge command received.
    jmp *%rax                           # Jump to the address given by wakeup_vector.


# NOTE: If we need to recover the VCPU index, we can do it in this way:
# TDCALL with "leaf number" 1 is a TDG.VP.TDINFO request. This gives us the
# number of CPUs and which is the current one (VCPU_INDEX). References:
#   - TDX Firmware Design Guide section 2.3.2
#   - TDShim https://github.com/confidential-containers/td-shim/blob/093d187c63ba91be81dee1fc8ef12fb169c08b7a/tdx-tdcall/src/lib.rs#L37
#   - TDShim https://github.com/confidential-containers/td-shim/blob/093d187c63ba91be81dee1fc8ef12fb169c08b7a/doc/tdshim_spec.md?plain=1#L101
#
# movq $1, %rax                        # Store value 1 in rax for TDCALL_TDINFO
# tdcall

# The results will be returned as (see Table 5.353 of Intel® TDX ABI Reference):
# R8  [31:0]  NUM_VCPUS
#     [63:32] MAX_VCPUS
# R9  [31:0]  VCPU_INDEX
