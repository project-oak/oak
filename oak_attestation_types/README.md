# Oak Attestation Types

Common traits and types for attestation in Project Oak.

## Overview

This crate defines the core abstractions used for generating and handling attestation evidence, endorsements, and assertions. It provides a standardized interface that different platform-specific attestation implementations (like Intel TDX, AMD SEV-SNP, or vTPM) can implement.

## Key Traits

- `Attester`: Trait for components that can generate attestation evidence.
- `Endorser`: Trait for components that provide signed endorsements for specific software or hardware versions.
- `AssertionGenerator`: Trait for creating assertions about the enclave's state or configuration.

## Design

The goal of this crate is to decouple the high-level attestation logic from the low-level, hardware-specific details. By using these traits, higher-level services can remain platform-agnostic while still benefiting from strong hardware-backed security.

See `src/attester.rs` for the `Attester` trait definition.
