# Endorscope CLI

Oak Transparent Release (TR) supports writing endorsement packages to Google
Cloud Storage (GCS) in a custom format which is not easily human-readable.
`endorscope_cli` is a command-line tool for listing and verifying such
endorsement packages on GCS. Currently the binary is available for Linux only.

## Getting the binary

The easiest way to use the tool is to download a pre-built Linux binary from the
GitHub Actions artifacts:

1. Open the
   [actions tab of the GitHub repo](https://github.com/project-oak/oak/actions)
2. Open a recent successful run of `build.yaml`
3. Scroll all the way down to _Artifacts_
4. Find, download and uncompress `endorscope_cli.zip`
5. Optional: Verify the included GitHub attestation
6. Install `endorscope_cli` in a location covered by your PATH variable

## Building from source

It is also possible to build the binary from source. However, this requires
[onboarding](https://github.com/project-oak/oak/blob/main/docs/development.md)
to the Oak repo first. Once this is done and `nix` is set up, run the following:

```bash
nix develop --command bazel build //tr/endorscope_cli
```

After that, the binary will be available at
`bazel-bin/tr/endorscope_cli/endorscope_cli`. It is also possible to invoke the
tool through bazel. In that case, use the following form:

```bash
nix develop --command bazel run //tr/endorscope_cli -- <command line arguments>
```

To run the integration tests (requires internet access to reach GCS):

```bash
nix develop --command bazel test //tr/endorscope_cli:tests --test_strategy=standalone
```

Since these tests are tagged as `["manual", "notap"]` they won't run as part of
standard automation.

## Usage

The tool provides two main commands: `list` and `verify`. Listing endorsements
always includes verification, so the former command does strictly more than the
latter.

### Global Options

The following options apply to all commands and subcommands:

- `--now-utc-millis`: Set the current time in milliseconds since the Unix Epoch.
  Defaults to the actual current time if not set.
- `--access-token`: Identity token for Cloud authentication. This is passed
  through to the HTTP calls and needed only when accessing a GCS setup that
  requires authentication.
- `--required-claims`: Claims that are required to be present on all
  endorsements. This is not used for filtering, but passed directly to
  endorsement verification. The entire call will fail whenever any of the
  verified endorsements does not possess the required claims.

### Listing Endorsements

The `list` command allows searching for endorsements by subject hash, endorser
key hash, or claim. An endorsement is only shown if it verifies correctly, which
includes verification of its validity against the timestamp provided via
`--now-utc-millis`, which defaults to the current time if not specified.
Example:

```bash
endorscope_cli --now-utc-millis=1759860000000 list \
  --fbucket=oak-files --ibucket=oak-index \
  --subject-hash=sha2-256:4e0acdea53c7004a03395317509a29b1a743719e02120a3a5af6f47505a1e14a \
  --limit=1
    ✅  sha2-256:340cf9f6432517af7161d905f0f62fd14cd2f7656dd18fc78e7cd90d7e59c2b4
        Subject:     sha2-256:4e0acdea53c7004a03395317509a29b1a743719e02120a3a5af6f47505a1e14a
        Not before:  2025-10-01T23:41:12.832Z
        Not after:   2025-10-31T23:41:12.832Z
```

The green checkmark indicates that the endorsement has passed verification. The
output includes the hash of the endorsement (same line), the hash of the
endorsement subject, and its validity period.

#### List Options

Mandatory options:

- `--fbucket`: Name of the GCS bucket that serves as content-addressable
  storage.
- `--ibucket`: Name of the GCS bucket containing the link index.

Providing at least one filtering option is mandatory, where all the provided
filtering options are concatenated by a logical AND:

- `--endorser-keyset-hash`: Filter by the hash of an endorser keyset.
- `--endorser-key-hash`: Filter by the hash of the endorser's public key.
- `--subject-hash`: Filter by the hash of the endorsed subject.
- `--claim`: Filter by a specific claim type.

Optional:

- `--limit`: Limit the number of endorsement packages to verify and return.
  Default value is 0 which means no limit.
- `--skip-tlog-verification`: Skips verification of transparency log inclusion.
  This comes in handy when you created endorsements which are not uploaded to
  Rekor.

### Verifying Endorsements

The `verify` command is a convenience CLI wrapper around the
`verify_endorsement::verify_endorsement` function. As the name suggests, it
performs a complete verification of an endorsement package. Endorsement packages
can either remain on GCS (subcommand: remote), or they are available on local
disk (subcommand: file).

#### Remote Verification

If the hash of the endorsement is known (likely from a previous `list` call),
then it can be verified directly from the remote storage. Example:

```bash
endorscope_cli --now-utc-millis=1759860000000 verify remote \
  --fbucket=oak-files --ibucket=oak-index \
  --endorsement-hash=sha2-256:eb8150f44a8e583a7f9e829d8855644b440c41d8ccc71df7a66002f6c0ca3a93
✅ OK
```

#### File Verification

This subcommand verifies an endorsement package available on a locally reachable
filesystem.

```bash
cd /path/to/endorsement/package
endorscope_cli verify file \
  --endorsement=endorsement.json \
  --signature=endorsement.json.sig \
  --endorser-public-key=public_key.pem \
  --rekor-log-entry=logentry.json
✅ OK
```
