# CTF SHA2: Oak Containers Challenge

This directory contains the Oak Containers variant of the SHA2 falsification
challenge.

## Background: Oak Containers

Oak Containers allows you to run unmodified container images in a Trusted
Execution Environment (TEE). The Orchestrator manages the lifecycle of the
application and provides cryptographic services, including attestation.

## The Challenge

The `enclave_app` running inside the container:

1. Generates a secret random flag.
2. Computes the SHA-256 digest of the flag.
3. Signs the digest using the enclave's signing key.
4. Returns the digest, the signature, and the attestation evidence.

The `host_app` launches the container and communicates with the `enclave_app` to
trigger this process.

## How to Participate

To run the challenge locally (using QEMU):

```bash
RUST_LOG=info bazel run //ctf_sha2/containers:host_app -- --vm-type=sev-snp
```

This will:

1. Build the container image.
2. Launch the Oak Containers Orchestrator and the Enclave App in QEMU.
3. Connect to the service.
4. Request a flag digest.
5. Print the returned digest and signature.

## Verification

See [The Arbiter](../README.md#the-arbiter) in the top-level README for
instructions on constructing the input and running the verification tool.
