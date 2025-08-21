# Endorsement for OCI Containers running in TEE

- **Status:** Reviewed
- **Date:** 2025-07-11

## Goal

This document proposes a design for producing and consuming endorsements for Oak
workloads running as OCI containers inside a Trusted Execution Environment
(TEE). The goal is to create a robust, platform-agnostic mechanism for clients
to verify the trustworthiness of a workload by validating a developer-signed
endorsement, rather than relying solely on platform-specific attestation
evidence. This process will leverage `cosign` for signing and storing
endorsements and Rekor for transparency.

## Background

### Oak Session

Oak Session provides a secure communication channel between a client and a
workload running in a Trusted Execution Environment (TEE). It relies on
attestation to verify the identity and integrity of the workload.
[Oak Session README](https://raw.githubusercontent.com/project-oak/oak/refs/heads/main/oak_session/README.md).

### TEE-based OCI Runtimes

This design applies to any TEE platform that can run OCI-compliant containers
and provide cryptographic attestation for the running workload. Major cloud
providers have offerings that follow this pattern:

- **Google Cloud Confidential Space:** Uses AMD SEV to run container workloads
  in a hardened environment.
- **Azure Confidential Containers:** Runs on Azure Container Instances (ACI) or
  Azure Kubernetes Service (AKS) using either AMD SEV-SNP or Intel TDX.
- **AWS Nitro Enclaves:** Provides isolated TEEs that can be used with services
  like EKS and ECS to run containerized applications.

In all these cases, the platform provides a mechanism for the running workload
to fetch **Platform Evidence**—a signed statement about the TEE's configuration
and the identity of the software running within it.

#### Platform Evidence

The format of the attestation evidence is specific to each TEE platform. It
could be a hardware quote, a certificate chain, or a structured token like a
JSON Web Token (JWT). Regardless of the format, for this framework to function,
the evidence must securely convey at a minimum:

- The identity of the running container image (e.g., a digest).
- The identity of the platform itself, rooted in a trust anchor like a vendor's
  CA.

For example, Google Cloud's Confidential Space provides a JWT that includes the
`image_reference` and `image_digest` in its claims, signed by a certificate
chain rooted in Google's CA. The following is an example of such a token:

```json
{
  "aud": "oak://session/attestation",
  "iss": "https://confidentialcomputing.googleapis.com",
  "sub": "https://www.googleapis.com/compute/v1/projects/oak-examples-477357/zones/us-west1-b/instances/echo-3ncl4v3",
  "eat_profile": "https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims",
  "submods": {
    "container": {
      "image_reference": "europe-west1-docker.pkg.dev/oak-examples-477357/c0n741n3r-1m4635/echo_enclave_app:latest",
      "image_digest": "sha256:2f81b55712a288bc4cefe6d56d00501ca1c15b98d49cb0c404370cae5f61021a",
      "restart_policy": "Never",
      "args": ["/usr/local/bin/oak_gcp_examples_echo_enclave_app"]
    },
    "gce": {
      "project_id": "oak-examples-477357",
      "instance_name": "echo-3ncl4v3"
    }
  },
  "tdx": {
    "gcp_attester_tcb_status": "UpToDate"
  }
}
```

A detailed reference for all claims can be found
[in the token claims documentation](https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims?hl=en).

### Endorsements

Directly verifying the `image_digest` in the JWT from a client is impractical,
as it changes with every new release. A more flexible approach is to use
endorsements. An endorsement is a statement signed by a trusted party (e.g., the
developer) that attests to the validity and security properties of a specific
software artifact.

#### In-toto Attestations

To create these endorsements, we use
[in-toto attestations](https://github.com/in-toto/attestation/blob/main/spec/README.md),
a framework for creating verifiable claims about software artifacts. An in-toto
statement consists of a `subject` (the artifact being attested to), a
`predicateType` (the type of claim being made), and a `predicate` (the content
of the claim).

For our use case, we use a dedicated predicate defined by the Oak project (see
[definition](https://project-oak.github.io/oak/tr/endorsement/v1)). This
predicate is designed for the general purpose of endorsing any software
artifact. It allows us to express the specific security and validity claims we
care about.

Here is an example of an in-toto endorsement for a container image:

```json
{
  "_type": "https://in-toto.io/Statement/v1",
  "subject": [
    {
      "name": "europe-west1-docker.pkg.dev/oak-examples-477357/c0n741n3r-1m4635/echo_enclave_app",
      "digest": {
        "sha256": "2f81b55712a288bc4cefe6d56d00501ca1c15b98d49cb0c404370cae5f61021a"
      }
    }
  ],
  "predicateType": "https://project-oak.github.io/oak/tr/endorsement/v1",
  "predicate": {
    "issuedOn": "2025-07-07T06:44:22.459000Z",
    "validity": {
      "notBefore": "2025-07-07T06:44:22.459000Z",
      "notAfter": "2026-07-07T06:44:22.459000Z"
    },
    "claims": [
      {
        "type": "https://github.com/project-oak/oak/blob/main/docs/tr/claim/52637.md"
      }
    ]
  }
}
```

By matching the `subject` of the in-toto statement with the `image_reference`
and `image_digest` from the JWT's `submods.container` claim, we can establish
trust in the workload. The endorsement is then published to a transparency log
like Rekor for auditability and to prevent rollback attacks.

#### Cosign and Rekor

To implement this, we rely on two key components of the
[Sigstore](https://www.sigstore.dev/) project: `cosign` and `Rekor`.

- **Cosign:** [Cosign](https://docs.sigstore.dev/cosign/overview/) is a tool for
  signing software artifacts, most notably container images. It simplifies the
  process of signing and verifying containers. When an image is signed with
  `cosign`, the resulting signature is typically stored in the same OCI registry
  as the image itself, using a predictable naming scheme that makes the
  signature easily discoverable. `cosign` also supports storing these signatures
  in a separate repository, which allows for different access controls. For
  instance, the container image can remain in a private repository while its
  signatures are made public in a different one for verification purposes.

- **Rekor:** [Rekor](https://docs.sigstore.dev/rekor/overview/) is a public,
  immutable, append-only transparency log. Its purpose is to provide a
  tamper-resistant ledger for software supply chain metadata. When `cosign`
  signs an artifact, it can optionally upload the signature and associated
  metadata to Rekor. Rekor then provides a "Signed Entry Timestamp" (SET) as a
  promise that the entry was included in the log. Clients can verify this SET to
  ensure that the signature they are seeing has been publicly recorded.

  While the validity period in the endorsement itself helps prevent simple
  rollback attacks, the transparency log addresses a more subtle problem:
  split-view attacks. In such an attack, a malicious actor could present a
  valid, but perhaps compromised, endorsement to a specific client or a small
  subset of clients, while hiding it from others.

  Rekor's public, append-only nature prevents this by ensuring that any
  endorsement a client verifies has been published to a globally visible and
  auditable log. A client can thus be sure that it is not being shown a private,
  one-off endorsement. The log's history is verifiable and can be monitored for
  inconsistencies, providing a strong guarantee of the integrity and public
  nature of the recorded signatures.

## Detailed Design

The proposed solution involves three main parts: producing and signing
endorsements, storing them in an OCI registry, and verifying them in the client.

### 1. Endorsement Generation and Signing

Developers will need a simple and reliable way to create and sign endorsements
for their container images. This process involves two main steps: generating the
in-toto statement and signing it with `cosign`.

#### 1.1. The `doremint` Crate: A Shared Library and CLI

The project already has a robust implementation for parsing and validating
in-toto statements located in the `@oak_attestation_verification` crate. To make
this functionality reusable, we will refactor it into a new crate named
`doremint`.

The `doremint` crate will serve two purposes:

1. **Library (`/src/lib.rs`):** It will provide the core, serializable structs
   for `Statement`, `Predicate`, and `Subject`. This library will be used by
   `@oak_attestation_verification` for parsing and validation.
2. **CLI Tool (`/main/main.rs`):** It will include a binary with a subcommand
   structure to support endorsing different artifact types in the future (e.g.,
   `doremint image endorse`). For providing the list of claims, which can be
   long and structured, the tool will accept a path to a TOML configuration
   file. This avoids clunky command-line flags for complex data.

   For example, a developer could create a `claims.toml` file to list a reusable
   set of claims:

   ```toml
   # See https://github.com/project-oak/oak/blob/main/docs/tr/claim/README.md
   # for more information on the meaning of individual claims.
   claims = [
       # The binary has been published.
       "https://github.com/project-oak/oak/blob/main/docs/tr/claim/52637.md",
   ]
   ```

   This approach consolidates the in-toto logic into a single, well-defined
   crate. It provides a user-friendly and extensible tool for developers to
   generate the endorsement statement. The signing of this statement is handled
   by a separate tool, as described in the next section. A future improvement
   could involve integrating `cosign`'s functionality as a library with the
   `cosign-rs` crate. This would create a single, streamlined command for
   developers (e.g., `doremint image sign`) that handles both statement
   generation and signing, abstracting away the underlying OCI and Reko
   interactions.

#### 1.2. Signing with Cosign

Once the `doremint` tool generates the in-toto statement, the `cosign` tool will
be used to sign it and associate it with the container image in the OCI
registry.

A critical aspect of this process is the management of the signing keys.
`cosign` supports a variety of key storage options, including local files,
hardware tokens (via PKCS#11), and cloud-based KMS providers. For more details,
see the
[`cosign` documentation on key storage](https://docs.sigstore.dev/cosign/signing/signing_with_containers/#sign-with-a-key-pair-stored-elsewhere).
Additionally, `cosign` offers a "keyless" signing mode that uses short-lived
certificates from the Fulcio certificate authority.

It is important to note that the default payload format for `cosign sign` is a
simple JSON object defined by the
[Simple Signing spec](https://github.com/sigstore/cosign/blob/main/specs/SIGNATURE_SPEC.md#simple-signing).
While `cosign` provides the `attest` command for creating in-toto attestations,
we are intentionally using the lower-level `sign --payload` command. The
`attest` command is designed for simpler predicates and does not offer the
flexibility needed for our custom, structured Oak endorsement predicate. Using
`sign --payload` gives us complete control over the in-toto statement that gets
signed, ensuring we can include all necessary structured claims.

Example command flow:

```bash
# 1. Generate the statement using the doremint tool.
# The image-specific details are passed as flags, while the reusable
# claims are loaded from a file.
doremint image endorse \
  --image-ref=europe-west1-docker.pkg.dev/oak-examples-477357/c0n741n3r-1m4635/echo_enclave_app \
  --image-digest=sha256:2f81b55712a288bc4cefe6d56d00501ca1c15b98d49cb0c404370cae5f61021a \
  --valid-for=365d \
  --claims-file=claims.toml \
  > statement.json

# 2. Sign the statement with cosign
IMAGE=europe-west1-docker.pkg.dev/oak-examples-477357/c0n741n3r-1m4635/echo_enclave_app@sha256:2f81b55712a288bc4cefe6d56d00501ca1c15b98d49cb0c404370cae5f61021a
cosign sign --key developer.key --payload statement.json $IMAGE
```

This flow separates the concern of statement generation (handled by our robust
`doremint` tool) from the signing and publishing (handled by the standard
`cosign` tool).

### 2. Endorsement Storage in OCI Registry

`cosign` stores the signature and associated metadata as a separate OCI image
with a predictable tag based on the digest of the signed image (e.g.,
`sha256-....sig`). The manifest for this signature image contains the signature
and the Rekor bundle in its layers and annotations.

Here is an example of such a manifest:

```json
{
  "schemaVersion": 2,
  "mediaType": "application/vnd.oci.image.manifest.v1+json",
  "config": {
    "mediaType": "application/vnd.oci.image.config.v1+json",
    "size": 233,
    "digest": "sha256:983f9da3ed42a6a919a0af50f6adcfd07310c489fac40405bc97bc92288de8a9"
  },
  "layers": [
    {
      "mediaType": "application/vnd.dev.cosign.simplesigning.v1+json",
      "size": 779,
      "digest": "sha256:94f907f57f60d71d6e21660b1bf4f2449281477a1bcf8e8552d92cc133facbfc",
      "annotations": {
        "dev.cosignproject.cosign/signature": "MEYCIQChTb4S9cl+PVHJbS8jkcUHAtGPaT7iuxRY1D0SIlEDRAIhAJuHzM/AZKQHb/76XTKFI+x3b6ClaXwDrKsa2uTkLTuy",
        "dev.sigstore.cosign/bundle": "{\"SignedEntryTimestamp\":\"MEQCIE5FqLPk9VMvWozUnCKR7evcgdjlYrWEAml9YXT9gUnkAiAZIQq/HJw5UgkTc0R6py1pk6+gQo5lx4rzg9bUNvuK4A==\", ...}"
      }
    }
  ]
}
```

The `layers[0].digest` is the SHA256 digest of the payload that was signed (our
in-toto statement). The
`layers[0].annotations["dev.cosignproject.cosign/signature"]` contains the raw
developer signature of that payload.

The `layers[0].annotations["dev.sigstore.cosign/bundle"]` contains the Rekor
bundle as a JSON string. This bundle includes the `SignedEntryTimestamp`, which
is a promise from Rekor that the entry was included in the log, and it can be
verified offline.

### 3. Verification in the Client

The client-side verification process involves several distinct stages to
establish trust in the workload.

#### 3.1. Platform Evidence Verification

Before inspecting any claims, the client must first verify the authenticity and
validity of the received platform evidence. The exact steps are
platform-specific, but generally involve:

- Verifying the evidence's signature against a known trust anchor for the TEE
  platform (e.g., a vendor's root CA).
- Checking the validity period of the evidence and any associated certificates.
- Parsing the evidence to extract the container image digest.

#### 3.2. Endorsement Acquisition

Once the platform evidence is trusted, the client needs to obtain the
developer's endorsement. There are two possible approaches:

- **Client-side Pull:** The client parses the image digest from the platform
  evidence and uses it to fetch the corresponding `cosign` signature directly
  from the OCI registry. This requires the client to have network access to the
  registry and to implement the OCI client logic.
- **Server-side Push:** The workload fetches its own endorsement from the OCI
  registry and sends it to the client along with the platform evidence. This is
  a more common pattern in Oak Sessions, as it simplifies the client's logic and
  reduces its network exposure.
- **Hybrid Push/Pull (Digest-based):** A middle ground that combines elements of
  both models. The server sends the _digests_ of the endorsement artifacts (in
  this case, the OCI bundle with the signature) to the client. Since the OCI
  registry is a Content-Addressable Storage (CAS) system, the client can fetch
  them if needed. This approach allows the client to efficiently cache
  endorsements and their verification status, which is particularly useful when
  endorsements are large, and workloads change infrequently.

#### 3.3. Endorsement Verification

After obtaining the endorsement, the client performs a series of cryptographic
checks.

##### 3.3.1. Subject Matching

The client must verify that the `subject` in the in-toto statement matches the
`image_reference` and `image_digest` from the now-trusted JWT. This ensures the
endorsement applies to the specific workload that was attested to.

##### 3.3.2. Developer Signature Verification

The client must verify the developer's signature on the endorsement. This is
done by checking the `dev.cosignproject.cosign/signature` from the OCI manifest
against the `digest` of the in-toto statement, using the developer's public key.

##### 3.3.3. Rekor Inclusion Verification

Finally, the client verifies the Rekor bundle to confirm the endorsement was
published to the transparency log. This is a critical step to prevent rollback
attacks and can be done offline without contacting Rekor. The process is as
follows:

1. **Parse the Bundle:** The client parses the `dev.sigstore.cosign/bundle`
   annotation from the OCI manifest. This contains the `SignedEntryTimestamp`
   (the signature from Rekor) and the `Payload` (the data that was signed).

2. **Canonicalize the Payload:** The `Payload` object must be canonicalized into
   a JSON string. This means all whitespace is removed and all object keys are
   sorted alphabetically. This step is critical, as the Rekor signature was
   computed over this exact string representation.

   Example of a canonicalized payload:

   ```json
   {
     "body": "eyJhcGlWZXJzaW9uIjoiMC4wLjEiLCJraW5kIjoiaGFzaGVkcmVrb3JkIiwic3BlYyI6eyJkYXRhIjp7Imhhc2giOnsiYWxnb3JpdGhtIjoic2hhMjU2IiwidmFsdWUiOiI5NGY5MDdmNTdmNjBkNzFkNmUyMTY2MGIxYmY0ZjI0NDkyODE0NzdhMWJjZjhlODU1MmQ5MmNjMTMzZmFjYmZjIn19LCJzaWduYXR1cmUiOnsiY29udGVudCI6Ik1FWUNJUUNoVGI0UzljbCtQVkhKYlM4amtjVUhBdEdQYVQ3aXV4UlkxRDBTSWxFRFJBSWhBSnVIek0vQVpLUUhiLzc2WFRLRkkreDNiNkNsYVh3RHJLc2EydVRrTFR1eSIsInB1YmxpY0tleSI6eyJjb250ZW50IjoiTFMwdExTMUNSVWRKVGlCUVZVSk1TVU1nUzBWWkxTMHRMUzBLVFVacmQwVjNXVWhMYjFwSmVtb3dRMEZSV1VsTGIxcEplbW93UkVGUlkwUlJaMEZGUldzM1dFTmFUMnBuWmtWeVZucGtOWGx4TlVkQlQyYzVSRlozY3dwdk4wdHBkemxPUlRFelNGUlFVRmRXUjBSVmR6TnVZV05IT1dRM2EzRjBlbE5KV2tOblRqUldaekJsTTJkUVlqTmFXRE56YTFkdVNFbDNQVDBLTFMwdExTMUZUa1FnVUZWQ1RFbERJRXRGV1MwdExTMHRDZz09In19fX0=",
     "integratedTime": 1752146045,
     "logID": "c0d23d6ad406973f9559f3ba2d1ca01f84147d8ffc5b8445c224f98b9591801d",
     "logIndex": 270155307
   }
   ```

3. **Verify the Signature:** The client verifies the `SignedEntryTimestamp` (a
   base64-encoded signature) against the canonicalized `Payload` string using
   Rekor's public key.

   Rekor's public key is a long-term key that changes infrequently. Key rotation
   is a manual, high-ceremony event tied to Sigstore's TUF root signing process,
   meaning clients can treat the key as a stable trust anchor. The public key
   can be fetched from the public Rekor instance (e.g.,
   `https://rekor.sigstore.dev/api/v1/log/publicKey`) or packaged with the
   client.

4. **(Optional) Online Inclusion Proof:** As a basic online check, a client can
   take the `logID` and `logIndex` from the bundle and query the Rekor API for
   an inclusion proof. This proves that the specific entry is part of the log's
   Merkle tree at that point in time. This is useful for stateless clients that
   cannot store information between sessions.

5. **(Optional) Online Consistency Proof:** For the strongest guarantee, a
   stateful client should verify the log's consistency over time. The client
   stores the log's Signed Tree Head (STH) locally after its first verification.
   On subsequent verifications, it fetches the latest STH and requests a
   _consistency proof_ from the log between the stored STH and the new one. This
   cryptographically proves that the log has only grown (append-only) and that
   its history has not been altered, protecting against split-view attacks where
   a log might show different versions to different clients.

### 4. Endorsement Proto Format

The canonical representation for a developer's endorsement is the
`SignedEndorsement` message from `proto/attestation/endorsement.proto`.

```protobuf
message SignedEndorsement {
  // The underlying unsigned endorsement, serialized as a JSON in-toto
  // statement.
  Endorsement endorsement = 1;

  // The signature over `endorsement.serialized`.
  Signature signature = 2;

  // The Rekor log entry about the endorsement.
  bytes rekor_log_entry = 3;
}
```

This message encapsulates all the components of the developer's endorsement: the
in-toto statement itself, the developer's signature over it, and the Rekor
transparency log entry.

How this `SignedEndorsement` message is transported to the client alongside the
platform-specific evidence is an integration detail for each TEE platform's
implementation. For example, in the server-push model, the workload would fetch
the data to populate this message and send it to the client along with the
platform's attestation evidence.
