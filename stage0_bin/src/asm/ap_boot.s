.code16
.section .ap_text, "ax"
# Entry point for APs. This needs to be page-aligned.
.align 4096
.global ap_start
ap_start:
    # Let the BSP know we're alive.
    lock incl (LIVE_AP_COUNT)
1:
    hlt
    jmp 1b

# Under SEV-ES, we need to use the AP Reset Hold and AP Jump Tables. We could munge all of it into
# `ap_start` above, but it's simpler to keep it separate as if we ever run this code we know we're
# under SEV-ES without risking any exceptions (and thus avoid the need for an IDT).
.global sev_es_start
sev_es_start:
    lock incl (LIVE_AP_COUNT)
1:
    xor %edx, %edx          # EDX = 0x0
    mov $0x006, %eax        # EAX = 0x007 - AP Reset Hold
    mov $0xC0010130, %ecx   # ECX = 0xC001_0130 -- GHCB MSR
    wrmsr                   # MSR[ECX] = EDX:EAX
    rep vmmcall             # VMGEXIT
    rdmsr                   # EDX:EAX = MSR[ECX]
    # Check return value: GHCBData[63:12] must be non-zero, GHCBData[12:0] must be 0x007
    mov %eax, %ebx          # EBX = EAX
    and $0xFFF, %ebx        # EBX |= 0xFFF (leave lowest 12 bits)
    cmp $0x007, %ebx        # is the response AP Reset Hold Response?
    jne 1b                  # No. Go back to sleep.
    and $-0xFFF, %eax       # EAX |= ~0xFFF (mask lowest 12 bits)
    add %edx, %eax          # EAX += EDX
    test %eax, %eax         # is GHDBData[63:12] zero?
    je 1b                   # Yes. Go back to sleep.
    # Determine where to jump from the AP Jump Table and off we go
    # First is IP, second is CS
    mov $AP_JUMP_TABLE, %sp # treat the jump table as stack
    iret                    # pop IP, pop CS, pop EFLAGS
    # if we're still here, something has gone wrong
    xor %edx, %edx          # EDX = 0x0
    mov $0x100, %eax        # EAX = 0x100 - Termination Request
    mov $0xC0010130, %ecx   # ECX = 0xC001_0130 -- GHCB MSR
    wrmsr                   # MSR[ECX] = EDX:EAX
    rep vmmcall             # VMGEXIT
1:                          # If we're still alive, just go into a HLT loop.
    hlt
    jmp 1b
