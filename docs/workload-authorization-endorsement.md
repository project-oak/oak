# Workload Authorization & Operator Signed Endorsements

This guide describes how to configure cryptographic workload authorization
across Confidential Computing deployments using **Operator-Level Signed
Endorsements**.

## 1. Separation of Roles: Operator vs. Delegated Signer

When deploying confidential workloads, it is critical to distinguish between
**supply chain build provenance** (`SignedEndorsement`) and **operational
cluster authorization** (`AuthorizedEndorsement`):

1. **Software Vendor / Builder (`oak_transparent_release`)**:
   - Issues a `SignedEndorsement` (`endorsement.json` + `.sig`) during artifact
     compilation to certify supply chain integrity
     (`"Was this binary compiled from verified source code without tampering?"`).
   - Evaluated dynamically over the wire during attestation handshakes.
2. **Workload Operator (Cluster Owner)**:
   - Deploys workloads and configures attestation verifiers (`oak_proxy`).
   - Does **not** need to hold private signing keys. Instead, the operator bakes
     an immutable public verification key (`endorsement_verifying_key.pem`)
     directly into the container image at build time, and mounts dynamic
     endorsement files (`authorized_endorsement.json` + `.sig`) at runtime.
3. **Delegated Endorsement Signer (SecOps / Release Authority)**:
   - An authority delegated by the Workload Operator holding the private signing
     key (optional; the Workload Operator may directly hold this role themselves
     if delegation to a separate security/release authority is not required).
   - After container images finish building and their digests (`sha256:...`) are
     finalized, the Endorsement Signer signs a detached `endorsement.json`
     authorizing those exact digests to communicate within the cluster
     (`"Are these specific image builds authorized to communicate in this deployment cluster today?"`).

## 2. Resolving Bidirectional Circular Build Dependencies

If an operator attempts to secure bidirectional communication between two
enclaves (`client` $\leftrightarrow$ `server`) by hardcoding static peer digests
(`authorized_image_digests`) inside `client.toml` and `server.toml`, an
unsatisfiable circular build dependency occurs:

- Building `client` requires the exact sha256 digest of `server`.
- Building `server` requires the exact sha256 digest of `client`.
- Modifying a configuration file inside either container alters its own sha256
  digest, breaking the peer's allowlist.

By delegating authorization to detached signed endorsements
(`authorized_endorsement_path`), container images bake in **only** the static
public verification key (`authorized_endorsement_verifying_key_pem_path`). After
both container images are built, the release pipeline signs
`authorized_endorsement.json` containing the final sha256 digests of both
artifacts, completely decoupling image compilation from peer digest
authorization.

## 3. Operational Workflow & Runtime Mounting (Confidential Space)

> [!NOTE] Currently, operator signed endorsement verification
> (`authorized_workload_endorsement`) is implemented and supported specifically
> for Google Cloud Confidential Space
> (`[attestation_verifiers.confidential_space]`).

1. **Key Generation**: Generate a P-256 ECDSA or Ed25519 signing keypair
   (`endorsement_key.pem` and `endorsement_pub.pem`). Bake `endorsement_pub.pem`
   into the base container image (e.g., at
   `/etc/proxy/endorsement_public_key.pem`).
2. **Endorsement Authoring & Signing**: Create `authorized_endorsement.json`
   conforming to the [Endorsement Specification V1](./tr/endorsement_v1.md)
   (`https://project-oak.github.io/oak/tr/endorsement/v1`), ensuring valid
   `notBefore` and `notAfter` timestamps and claim type
   `https://project-oak.github.io/oak/tr/claim/confidential_space_image/v1`.
   Sign the statement using standard cryptographic utilities such as OpenSSL
   (`openssl dgst -sha256 -sign endorsement_key.pem -out authorized_endorsement.sig authorized_endorsement.json`)
   or automated release CI pipelines to produce `authorized_endorsement.sig`.
3. **Dynamic Runtime Fetching**: At startup, the running container workload can
   dynamically fetch the detached `authorized_endorsement.json` and
   `authorized_endorsement.sig` over network transport mechanisms (such as
   HTTPS/web fetch or cloud object storage like Google Cloud Storage) and place
   them at the paths configured inside `proxy.toml`.
4. **Attesting Fetch Parameters (`tee-` Metadata)**: When passing configuration
   variables (such as endorsement download URLs or GCS bucket paths) into a
   Confidential Space instance via instance metadata (`metadata`), it is
   strongly advisable to prefix those variable names with **`tee-`** (e.g.,
   `tee-endorsement-url`). In Google Cloud Confidential Space, any instance
   metadata attribute prefixed with `tee-` is automatically bound into the
   enclave's cryptographic attestation claims, ensuring that remote verifiers
   and auditing services can attest exactly what endorsement configuration
   sources the container was booted with. Once fetched,
   `AuthorizedEndorsement::load()` verifies the endorsement signature against
   the baked-in `endorsement_public_key.pem` and enforces the allowed container
   digests during peer attestation.
