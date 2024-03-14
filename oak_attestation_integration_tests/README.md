# Oak Attestation Integration Tests

Tests that cover the full workflow of generating an attestation to then
verifying it.

These tests are kept in a seperate crate as they rely on a set of different
crates, some which are and some of which are not available in google3. Tests for
individual aspects of the attestation/verification flow that do not rely on
other crates should be kept in the relevant crate. This way they can be run in
google3 if the crate is imported.
