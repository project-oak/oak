# Oak Stage 0

The initial entry point for the Project Oak boot process.

## Overview

Stage 0 is the very first code that runs in the enclave after the hardware initialization. Its primary responsibilities include:

- **Hardware Initialization**: Setting up the CPU and memory environment (e.g., GDT, IDT, paging).
- **Attestation**: Initial measurements of the boot environment and the next boot stage.
- **DICE Implementation**: Deriving the first stage of the DICE identity and evidence.
- **Loading the Next Stage**: Loading and handing off control to the next boot component (usually the Restricted Kernel).

## Sub-Components

- `stage0_tdx`: Specific implementation for Intel TDX.
- `stage0_sev`: Specific implementation for AMD SEV-SNP.
- `stage0_parsing`: Logic for parsing the initial boot parameters.

## Design

Stage 0 is designed to be extremely minimal and runs as a `no_std` crate. It relies on direct hardware interaction and uses the `oak_dice` and `oak_attestation_types` crates to establish the initial trust anchor.

For the entry point logic, see `src/lib.rs`.
