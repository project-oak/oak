# endorse

This tool facilitates the creation and storage of cryptographic endorsements for
files, following the OCI Image Manifest Specification (OCI Layout). It uses
`cosign` for signing and organizes endorsements in a content-addressed manner.

## Features

- Generates SHA2-256 digests for input files (subjects).
- Utilizes `cosign sign-blob` to create Sigstore endorsement bundles.
- Stores both the original subjects and their endorsement bundles as
  content-addressed blobs in a `blobs/sha256` directory.
- Maintains a single `index.json` file at the repository root, compliant with
  the
  [OCI Image Manifest Specification](https://github.com/opencontainers/image-spec/blob/main/image-layout.md#indexjson-file).
- Annotates index entries with `tr.subject` (linking to the endorsed content)
  and `tr.type` (identifying as "subject" or "endorsement").

## Usage

```bash
# Ensure cosign is installed and in your PATH
# go install github.com/sigstore/cosign/cmd/cosign@latest

just build-endorse
./bin/endorse -file=<path_to_file_to_endorse> -repository=<path_to_endorsements_repo_root>
```

**Example:** If you have `my_app.bin` and want to endorse it into an OCI
repository at `./my_endorsements_repo`:

```bash
./bin/endorse -file=my_app.bin -repository=./my_endorsements_repo
```

This will create a structure similar to:

```text
./my_endorsements_repo/
├── blobs/
│   └── sha256/
│       ├── <sha256_digest_of_my_app.bin>
│       └── <sha256_digest_of_endorsement_bundle>
└── index.json
```

You can then push this to an upstream git repository.

## Dependencies

- [Cosign](https://docs.sigstore.dev/cosign/overview/) (must be installed and
  available in your system's PATH).
