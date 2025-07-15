# Sigstore Crate

## Purpose

This crate provides essential tools for verifying Sigstore signatures and transparency log
entries. Its primary goal is to enable secure software supply chain verification within
environments where the standard library (`std`) is not available, such as secure enclaves.

Verifying that a software artifact, like a container image, has been signed by a trusted party
and that the signature has been recorded in a public transparency log is a critical security
practice. This process increases confidence in the artifact's integrity and origin, and this
library provides the necessary tools to perform that verification in a `no_std` context.

Besides `no_std` compatibility, the other main difference with https://crates.io/crates/sigstore
is the support for custom payloads in the signature container other than `SimpleSigning`.

## Cosign Specification

[Cosign](https://github.com/sigstore/cosign/blob/main/specs/SIGNATURE_SPEC.md) standardizes how
signatures for OCI artifacts are stored and discovered. Instead of requiring a separate server
to store signatures, Cosign leverages the OCI registry itself.

The protocol works as follows:

1. When an artifact (e.g., a container image) is signed, a new OCI manifest is created for the
   signature payload.
2. This signature manifest is stored in the same repository as the artifact it signs.
3. It is identified by a unique tag derived from the digest of the original artifact. The
   convention is to replace the `sha256:` prefix with `sha256-` and append `.sig`. For
   example, an artifact with the digest `sha256:abc...` would have a signature with the tag
   `sha256-abc....sig`.
4. The signature itself, along with its associated Rekor bundle, is stored in the annotations
   of a layer within this signature manifest.

This crate implements a client for this specification, enabling it to locate and fetch signature
data for any OCI artifact.

## Rekor Specification

[Rekor](https://www.sigstore.net/rekor/overview) provides a public, immutable, append-only log
for software supply chain metadata. Its role is to provide a verifiable, timestamped record of
when a signature was created and made public. This prevents back-dating attacks and provides a
global audit trail.

The Rekor protocol involves the following:

1. When a client submits signature metadata, Rekor includes it in a new log entry.
2. Rekor then signs the entry's contents and metadata, producing a
   **Signed Entry Timestamp (SET)**. This is also known as an "inclusion promise."
3. A client can then verify this SET using Rekor's public key. This verification confirms that
   the log operator has received the entry at a specific time and has promised to include it
   in the public log. It authenticates the entry's content and timestamp against the log's
   identity.

This crate specifically supports the `HashedRekord` entry type, which contains the artifact's
cryptographic hash, the signature over that hash, and the public key used to create the
signature.

Note that this crate does not bundle Rekor's public key. It must be provided by the user and can
be obtained from [Rekor's public API](https://rekor.sigstore.dev/api/v1/log/publicKey).

## Design

- **`no_std` Compatible**: The crate is designed to work without the Rust standard library,
  making it suitable for use in embedded systems, WebAssembly, and other resource-constrained
  or specialized environments.
- **Modular**: The logic is separated into modules for `cosign` and `rekor`, reflecting the
  different components of the Sigstore ecosystem.
- **Structured Error Handling**: Errors are clearly defined and categorized, making it
  straightforward to handle verification failures and debug issues.
