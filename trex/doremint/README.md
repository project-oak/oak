# Do-Re-Mint Endorsement Tool

## Purpose

`doremint` is a command-line tool for creating and verifying endorsements for
container images. It provides a way to make falsifiable claims about a software
artifact, such as "this image has passed all integration tests" or "this image
was built by our trusted CI/CD pipeline."

These endorsements are a critical part of a secure software supply chain, as
they allow you to build and enforce policies based on verifiable metadata,
rather than just trusting the artifact itself.

## Functionality

The tool is split into two main subcommands: `image` and `blob`.

### `image`

Commands for working with OCI container images.

#### `image endorse`

This command creates a new, unsigned
[Transparent Release in-toto statement](https://project-oak.github.io/oak/tr/endorsement/v1)
for a container image. The statement includes the following fields:

- `issuedOn`: An RFC3339 timestamp indicating when the endorsement was created.
- `validity`: An object specifying the `notBefore` and `notAfter` timestamps
  that define the endorsement's validity period.
- `claims`: A list of objects, where each object has a `type` field containing a
  URI that represents a specific claim being made about the subject.

An in-toto statement is a JSON file that can then be signed and attached to an
image using the `cosign` tool.

#### `image verify`

This command verifies a signed endorsement against a container image. It
performs a complete, end-to-end verification of the software supply chain, which
includes:

1. **Fetching the Signature**: It pulls the Cosign signature for the specified
   image from the OCI registry.
2. **Verifying the Rekor Entry**: It verifies the inclusion signature from the
   Rekor transparency log, ensuring the signature was publicly logged.
3. **Verifying the Signature**: It cryptographically verifies that the signature
   was created by the private key of the developer of the container.
4. **Validating the Endorsement Statement**: It checks that:
   - The endorsement is still within its validity period.
   - The claims expected by the user are present among the claims in the
     endorsement.
   - The digest of the image matches the subject of the endorsement.

If all of these checks pass, the tool confirms that the endorsement is valid.

### `blob`

Commands for working with arbitrary blobs (files).

#### `blob endorse`

Endorses a file, creating a Transparent Release statement and storing it in a
local directory structure acting as an OCI repository.

#### `blob verify`

Verifies an endorsement for a blob by fetching it from an HTTP server serving
the OCI repository.

## Usage

### Endorsing an Image

The endorsement process is a two-step workflow involving both `doremint` and
`cosign`.

####  Step 1: Generate the Endorsement Statement

First, use `doremint` to create the unsigned endorsement statement:

```bash
doremint image endorse \
    --image=$IMAGE_REFERENCE \
    --claims-toml=$PATH_TO_CLAIMS_TOML \
    --valid-for=$VALIDITY_DURATION \
    --output=/path/to/endorsement.json
```

- `--image`: The OCI reference of the image to endorse (e.g.,
  `gcr.io/my-project/my-image@sha256:...`).
- `--claims-toml`: A TOML file containing a list of claims to include.
- `--valid-for`: How long the endorsement is valid (e.g., `30d`, `12h`, `1w`).
- `--output`: The path to write the unsigned endorsement statement to.

#### Step 2: Sign and Attach with Cosign

Next, use `cosign sign` with the `--payload` flag to sign the generated JSON
statement and attach it to the image. This single command handles signing,
creating the signature object, and uploading it to the OCI registry and to the
Rekor transparency log.

```bash
cosign sign --key=/path/to/private.key \
            --payload=/path/to/endorsement.json \
            $IMAGE_REFERENCE
```

**Note on Key Management**: The example above uses a local private key file
(`--key`). For production use, it is highly recommended to use a more secure key
management solution. `cosign` supports several advanced methods, including:

- **Cloud KMS**: Using a key managed by a cloud provider (e.g., Google Cloud
  KMS, AWS KMS, Azure Key Vault).
- **Keyless Signing**: Using short-lived certificates from a certificate
  authority like [Fulcio](https://www.sigstore.net/fulcio/overview), which ties
  the signature to a federated identity.

While `cosign` supports both, the `doremint verify` command currently requires a
specific public key for verification and does not yet support the keyless
workflow. For more details, see the
[Cosign documentation on signing](https://docs.sigstore.dev/cosign/signing).

### Sigstore Cosign

[Cosign](https://github.com/sigstore/cosign/blob/main/specs/SIGNATURE_SPEC.md)
standardizes how signatures for OCI artifacts are stored and discovered. Instead
of requiring a separate server to store signatures, Cosign leverages the OCI
registry itself.

The protocol works as follows:

1. When an artifact (e.g., a container image) is signed, a new OCI manifest is
   created for the signature payload.
2. This signature manifest is stored in the same repository as the artifact it
   signs.
3. It is identified by a unique tag derived from the digest of the original
   artifact. The convention is to replace the `sha256:` prefix with `sha256-`
   and append `.sig`. For example, an artifact with the digest `sha256:abc...`
   would have a signature with the tag `sha256-abc....sig`.
4. The signature itself, along with its associated Rekor bundle, is stored in
   the annotations of a layer within this signature manifest.

### Verifying an Endorsement

To verify a signed endorsement for an image:

```bash
doremint image verify \
    --image=$IMAGE_REFERENCE \
    --endorser-public-key=$PATH_TO_PUBLIC_KEY_PEM \
    --claims-toml=$PATH_TO_CLAIMS_TOML
```

- `--image`: The OCI reference of the image to verify.
- `--endorser-public-key`: The public key that was used to sign the endorsement.
- `--claims-toml`: A TOML file containing the list of claims that you expect the
  endorsement to have.

**Note on Rekor's Public Key**: `doremint` includes Rekor's public key to verify
the transparency log's inclusion promise. In the very unlikely event that Rekor
rotates its key, this tool must be updated. The key can be obtained from
[Rekor's public API](https://rekor.sigstore.dev/api/v1/log/publicKey).

## Endorsing and Verifying Blobs (E2E Example)

This section demonstrates how to endorse a local file (blob) and then verify
that endorsement using `doremint`.

### Prerequisites

- `doremint` built and available in your path.
- Python 3 (for running a simple HTTP server).
- `cosign` installed and configured (specifically for identity-based signing,
  which `doremint blob endorse` uses internally).

### 1. Setup

Create a temporary directory for the example:

```bash
mkdir --parents /tmp/doremint-demo/repo
cd /tmp/doremint-demo
```

Create a dummy file to endorse:

```bash
echo "Hello, secure world!" > /tmp/artifact.txt
ARTIFACT_DIGEST=$(sha256sum /tmp/artifact.txt | awk '{print "sha256:" $1}')
echo "Artifact Digest: $ARTIFACT_DIGEST"
```

### 2. Endorse the Blob

Run `doremint blob endorse` to sign the artifact and store the endorsement in
the local repository structure.

```bash
bazel run trex/doremint -- \
  blob endorse \
  --file=/tmp/artifact.txt \
  --repository=/tmp/endorsements \
  --claims=test \
  --valid-for=1d
```

This command will:

1. Read `artifact.txt`.
2. Create an endorsement statement with the specified claim valid for 1 day
   (`1d`).
3. Sign the statement using `cosign` (this might trigger an OIDC authentication
   flow in your browser).
4. Store the artifact, the statement, and the signature in `./repo` formatted as
   an OCI repository.

You can check the resulting repository structure:

```console
$ tree /tmp/endorsements
/tmp/endorsements
├── blobs
│   └── sha256
│       ├── 4e79a01a8c7e93013a8980c189dc9555bf535001411e9996cbde3d0d27b0d866
│       ├── 6af6ffef11abef73607f5a72ca6f068af1fd2941298615bea2111a68456d31d0
│       └── 77356716220225abedf3dad1a4291f035cd26f279208d1d279feff56f2c362cb
└── index.json
```

### 3. Serve the Repository

Start a simple HTTP server to serve the repository content. Open a new terminal
window:

```bash
cd /tmp/endorsements
python3 -m http.server 8080
```

### 4. Verify the Endorsement

Now, verify the endorsement using `doremint blob verify`. You need to know the
identity used to sign the blob (e.g., your email address and the issuer).

```bash
bazel run trex/doremint -- \
  blob verify \
  --subject-digest=$ARTIFACT_DIGEST \
  --http-index-url=http://localhost:8080/index.json \
  --claims=test \
  --cosign-identity="your.email@example.com" \
  --cosign-oidc-issuer="https://accounts.google.com"
```

Replace `your.email@example.com` and the issuer with the actual values used
during the signing process (which `cosign` typically prints or you know from
your OIDC provider).

If successful, you should see output indicating "Verification successful!" and
details about the endorsement.
