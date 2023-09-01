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
