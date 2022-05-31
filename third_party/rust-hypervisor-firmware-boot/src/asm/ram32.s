.section .text32, "ax"
.global ram32_start
.code32

ram32_start:
    # Stash the boot metadata struct in %rdi.
    movl %ebx, %edi
    # If present, the multiboot magic is in %eax; move it to %esi.
    movl %eax, %esi

setup_page_tables:
    # First L3 entry identity maps [0, 1 GiB)
    movl $0b10000011, (L3_TABLE)
    # First L4 entry points to L3 table
    movl $L3_TABLE, %eax
    orb  $0b00000011, %al # writable (bit 1), present (bit 0)
    movl %eax, (L4_TABLE)
/*
    # First L2 entry identity maps [0, 2 MiB)
    movl $0b10000011, (L2_TABLES) # huge (bit 7), writable (bit 1), present (bit 0)
    # First L3 entry points to L2 table
    movl $L2_TABLES, %eax
    orb  $0b00000011, %al # writable (bit 1), present (bit 0)
    movl %eax, (L3_TABLE)
    # First L4 entry points to L3 table
    movl $L3_TABLE, %eax
    orb  $0b00000011, %al # writable (bit 1), present (bit 0)
    movl %eax, (L4_TABLE)
*/

enable_paging:
    # Load page table root into CR3
    movl $L4_TABLE, %eax
    movl %eax, %cr3

    # Set CR4.PAE (Physical Address Extension)
    movl %cr4, %eax
    orb  $0b00100000, %al # Set bit 5
    movl %eax, %cr4
    # Set EFER.LME (Long Mode Enable)
    movl $0xC0000080, %ecx
    rdmsr
    orb  $0b00000001, %ah # Set bit 8
    wrmsr
    # Set CRO.PG (Paging)
    movl %cr0, %eax
    orl  $(1 << 31), %eax
    movl %eax, %cr0

jump_to_64bit:
    # We are now in 32-bit compatibility mode. To enter 64-bit mode, we need to
    # load a 64-bit code segment into our GDT.
    lgdtl GDT64_PTR
    # Initialize the stack pointer (Rust code always uses the stack)
    movl $stack_start, %esp
    # Push 8 bytes to fix stack alignment issue. Because we enter rust64_start
    # with a jmp rather than a call the function prologue means that the stack
    # is no loger 16-byte aligned.
    pushl $0
    pushl $0
    # Set segment registers to a 64-bit segment.
    movw $0x10, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %gs
    movw %ax, %fs
    movw %ax, %ss
    # Set CS to a 64-bit segment and jump to 64-bit Rust code.
    # PVH start_info is in %rdi, the first paramter of the System V ABI.
    ljmpl $0x08, $rust64_start

