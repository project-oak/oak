# Transparent Release

The goal of release transparency is to provide certainty about binaries all the
way from being compiled and linked from source code to their final deployment.
Certainty cannot come from hand-wavy promises: it must be based on cryptographic
verifiability. In that way the risk of software supply chain attacks is
drastically mitigated.

The life of a binary can be divided into three phases \- _before, during and
after release_. Before release, i.e. up to and including compilation and
linking, we must make sure the expected source code is built using the expected
tools without any interference. During a release, we once more verify the
integrity of the build results and then generate an endorsement, sign it, and
upload it to an external append-only log. After release, the binary and all
associated metadata are immutable. The user must be sure that the binary is not
altered on the way from the developer to the location of deployment. Therefore,
prior to any use, the binaries are checked via attestation or endorsement
verification.

The developer’s requirements and needs for building and making releases are
extremely variable. Therefore, we don’t publish tools for the first two phases:
before and during release. However, we describe the process and data formats so
that the interface to the post-release phase (which consists e.g. of Oak’s
attestation verification library) is unambiguous.

## Before release

Given the source code in a repository, a trusted builder generates the binary
and a provenance (e.g. a GitHub attestation). The provenance is signed by the
trusted builder and contains all information needed in order to retry the build.

A binary is reproducibly buildable whenever the subsequent build attempts (not
necessarily by the trusted builder) yields bitwise the same binary. Even to a
third party, reproducing the exact same binary using the same source code and
builder is possible. Reproducible builds are highly desirable. Oak's own
critical binaries are [reproducibly buildable](reproducible.md).

## During release

For release, the developer must make sure that any continuous integration passes
and the provenance generated in the previous step is valid. Then the developer
creates an endorsement and signs it with their own signing key for that binary.
Along with the timestamp this signature is persisted in the Rekor transparency
log. Summarizing, releasing a binary is the same as generating all this side
data and making the entire binary package discoverable for deployment.

### Endorsement

Current endorsements are in-toto statements, encoded as JSON following
[Oak’s endorsement schema](https://project-oak.github.io/oak/tr/endorsement/v1).
Here is a full example:

```jsonc
{
  "\_type": "https://in-toto.io/Statement/v1",
  "predicateType": "https://project-oak.github.io/oak/tr/endorsement/v1",
  "subject": \[{
    "name": "oak_functions_container",
    "digest": {
      "sha256": "5f0c567cb98ad3cf2c486a304c1fcf7e414348752cf7dc427ef154a5842f0be9"
    }
  }\],
  "predicate": {
    "issuedOn": "2024-10-18T10:45:36.376000Z",
    "validity": {
      "notBefore": "2024-10-18T10:45:36.376000Z",
      "notAfter": "2025-10-18T10:45:36.376000Z"
    },
    "claims": \[{
      "type": "https://github.com/project-oak/oak/blob/main/docs/tr/claim/18136.md"
    }, {
      "type": "https://github.com/project-oak/oak/blob/main/docs/tr/claim/75606.md"
    }\]
  }
}
```

#### Validity

On top of the time of issuance, the endorsement contains a validity period which
is checked against the current time on each attestation or endorsement
verification. The validity period is freely configurable. The strategy for
revocation can be passive: simply issue endorsements with relatively short
validities, such that the binaries that should be revoked cease to be valid
relatively quickly.

#### Claims

The endorsement may contain zero or more additional claims about the binary. A
claim is represented by a
[type URI in the sense of in-toto](https://github.com/in-toto/attestation/blob/main/spec/v1/field_types.md#TypeURI).
We expect that the type URI is a URL which resolves to an accurate specification
of the claim. The idea is that the developer can make additional assertions
about properties of the binary. For example, if there are logging and
non-logging variants of the binary, the developer may use a claim to designate
the non-logging variants as more secure. The user can verify the presence of the
claims during attestation or endorsement verification.

Another purpose of the claims is to provide a simple and clear handshake between
the end user and a human code auditor who has access to closed source. Provided
the claim landscape covers all security concerns and claims are concretely
phrased, the auditor can just work down the list of claims. The user on the
other hand can verify and rely on the claims while not having access to the
source.

### Signature

The serialized endorsement is signed with an ECDSA P-256 signing key with
SHA2_256 hashing. The developer must take good care to protect the signing key
and process. The signature is saved along with the endorsement as
`endorsement.json.sig`.

### Transparency log

In addition, the hash of the endorsement and the signature are appended to the
Rekor transparency log. The receipt can be downloaded from Rekor and is saved as
`logentry.json`.

### Example on the command line

The following steps show how to do the release processing on the command line.
The data formats involved are compatible with Oak’s endorsement verification.
For all steps to work you'll need to download the Rekor CLI suitable for your
platform from
[https://github.com/sigstore/rekor/releases](https://github.com/sigstore/rekor/releases).

1. Generate a key pair consisting of a private signing key and a public
   verifying key.
   1. `openssl ecparam -genkey -name prime256v1 -noout -out private_key.pem`
   2. `openssl ec -in private_key.pem -pubout -out public_key.pem`
2. Build the binary. We assume that it is in a file named binary.
3. Create an endorsement with the digest of the binary and a validity period.
   Add claims as needed. Save the file as `endorsement.json`.
4. Sign the endorsement and verify the signature.
   1. `openssl dgst -sha256 -sign private_key.pem endorsement.json > endorsement.json.sig`
   2. `openssl dgst -verify public_key.pem -signature endorsement.json.sig endorsement.json`
5. Upload the signature and the public key to Rekor. Only the hash of the
   endorsement is uploaded, not the entire endorsement or artifact. The
   following command does this. It also outputs the serial number and a deep
   link to the log entry.
   1. `rekor-cli upload --rekor_server https://rekor.sigstore.dev --signature endorsement.json.sig --public-key public_key.pem --artifact endorsement.json --pki-format x509`
6. Download the inclusion proof from the link displayed and save it as
   `logentry.json`. Example:
   1. `curl https://rekor.sigstore.dev/api/v1/log/entries/24296fb24b8ad77acec475da677d0db5934e028e53a2bd9ad7f4af4574a6903f1ac279ba413fa930`
7. For completeness verify the log entry which requires the signature and the
   digest of the endorsement as inputs.
   1. `rekor-cli verify --rekor_server https://rekor.sigstore.dev --signature endorsement.json.sig --public-key public_key.pem --artifact endorsement.json --pki-format x509`

## After release

After release the binary can be deployed and used, but not without prior
verification of its endorsement.

### Discoverability

In general, discovery starts with the log entry. The log entry can be discovered
from Rekor, e.g. via the CLI. It contains the digest of the endorsement, which
in turn provides the digest of the binary. Building lookup facilities for these
items is up to the developer.

### Verification

Oak offers standalone endorsement verification which is also used as a building
block in attestation verification. Depending on the situation, the full
attestation verification may not be feasible in which case it is possible to
verify the endorsement directly. We describe how to convert the associated
metadata generated during release to inputs for endorsement verification. With
both SignedEndorsement and EndorsementReferenceValue it is straightforward to
call
[`oak_attestation_verification::verify_endorsement()`](https://github.com/project-oak/oak/blob/d4159dbc3c7c5b0881f4e03fada326f1b44c074f/oak_attestation_verification/src/lib.rs#L52).

#### SignedEndorsement

The metadata associated with the binary can be converted directly into a
SignedEndorsement, as follows:

```proto
endorsement {
  format: ENDORSEMENT\_FORMAT\_JSON\_INTOTO
  serialized: "\<contents of endorsement.json\>"
}
signature {
  key\_id: 1
  raw:  "\<contents of endorsement.json.sig\>"
}
rekor\_log\_entry: "\<contents of logentry.json\>"
```

#### EndorsementReferenceValue

It is important that at least one verifying key exists under the endorser field
that has the key ID of the signature that should be verified. The management of
the key IDs is the responsibility of the developer. The Rekor public key can be
downloaded from [Sigstore](https://rekor.sigstore.dev/api/v1/log/publicKey) and
is not versioned.

```proto
endorser {
  keys {
    type: KEY\_TYPE\_ECDSA\_P256\_SHA256
    key\_id: 1
    raw: "\<contents of public\_key.pem converted to raw\>"
  }
}
required\_claims: "\<required claim 1\>"
required\_claims: "\<required claim 2\>"
rekor {
  verify {
    keys {
      type: KEY\_TYPE\_ECDSA\_P256\_SHA256
      raw: "\<contents of rekor\_public\_key.pem converted to raw\>"
    }
  }
}
```
