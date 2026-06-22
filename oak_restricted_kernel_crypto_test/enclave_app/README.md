# AEAD Enclave App

Restricted Kernel binary that implements the `oak.crypto_test.Aead` micro_rpc
service using the [`aes-gcm`](https://crates.io/crates/aes-gcm) crate.

Supports AES-128-GCM and AES-256-GCM, selected automatically based on the key
length in each request.

This is the default implementation used by the
[crypto integration test](../README.md). To test an alternative crypto library,
create a new enclave app that implements the same
[`Aead` proto](../proto/aead.proto) and point the test's BUILD `data` dependency
at it.
