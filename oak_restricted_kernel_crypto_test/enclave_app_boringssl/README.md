# AEAD Enclave App (BoringSSL)

Restricted Kernel binary that implements the `oak.crypto_test.Aead` micro_rpc
service using [BoringSSL](https://boringssl.googlesource.com/boringssl/)'s
`EVP_AEAD` API via FFI bindings.

This is an alternative to the [`aes-gcm`-based enclave app](../enclave_app/)
that exercises the same Wycheproof test vectors against BoringSSL's AES-GCM
implementation. Both apps implement the identical
[`Aead` proto](../proto/aead.proto) service, so the
[crypto integration test](../README.md) can target either one by switching the
BUILD `data` dependency.

Supports AES-128-GCM and AES-256-GCM, selected automatically based on the key
length in each request.
