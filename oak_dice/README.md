# Oak DICE

Implementation of DICE-based (Device Identifier Composition Engine) attestation for Project Oak.

## Overview

DICE is a standard for providing a cryptographic identity to a device based on its hardware and the software it boots. This crate provides the building blocks for creating and verifying DICE-based attestation evidence in Oak.

## Components

- **Certificates**: Tools for generating and parsing DICE certificates (often encoded as CWT/CBOR).
- **Evidence**: Structures representing the DICE evidence chain, including the CDI (Compound Device Identifier) and various measurements.
- **Utilities**: Helper functions for key derivation (HKDF) and hash calculations used in the DICE flow.

## Design

The DICE flow in Oak typically involves deriving new layers of identity as the boot process progresses (e.g., from Stage 0 to the Restricted Kernel). Each stage measurements are mixed into the secret state to produce the next stage's identity.

For more details on the evidence format, see `src/evidence.rs`.
