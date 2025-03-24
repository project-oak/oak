# Oak build

## Per-commit build and provenance generation

Every time a pull-request is merged to `main` the binaries specified in
[/.github/workflows/build.yaml](/.github/workflows/build.yaml) are built and
uploaded to GCS. In addtion a provenance is generated for the binary and
uploaded to GCS as well. We use the GitHub attest action to generate
provenances, which end up on being published on
[SigStore](https://rekor.sigstore.dev).

## Adding a new binary

To add a new binary, a new buildconfig must be added to the build workflow. Once
added the new binary will be built and attested on each merge.

### Step 1: Add a buildconfig

A buildconfig is a bash script which exports a few environment variables and
appears in the [/buildconfigs](/buildconfigs) folder. The required variables are
the following:

- `PACKAGE_NAME`: The name of the Transparent Release package.
- `BUILD_COMMAND`: The command for building the binary that will be passed to
  `docker run`. It must be specified as a bash array.
- `SUBJECT_PATHS`: Array with the names of subjects that should be attested. The
  names are paths relative to the repository root. The first element of the
  array is required to be the main binary.

### Step 2: Add the buildconfig to the build workflow

Add the new buildconfig in
[/.github/workflows/build.yaml](/.github/workflows/build.yaml) as a new value
for the matrix variable `buildconfig`:

```yaml
jobs:
  build_attest_all:
    strategy:
      fail-fast: false
      matrix:
        buildconfig:
          - buildconfigs/key_xor_test_app.sh
          - buildconfigs/<name_of_the_new_buildconfig_file>
```

## Retrieving a previously built binary and provenance

To download, the SHA1 hash of the commit and the package name (the identifier of
the binary) are needed.

### Step 1: Download the binary

To download the binary, run the following on the command line.

```bash
fetch_file() {
  local hash="$1"
  local path="$2"
  curl --fail "https://storage.googleapis.com/oak-files/${hash}" --output "${path}"
  local actual_hash="sha2-256:$(sha256sum "${path}" | cut -d " " -f 1)"
  if [[ "${hash}" != "${actual_hash}" ]]; then
    exit 1
  fi
}

readonly BINARY_FOR_COMMIT=6
hash=$(curl "https://storage.googleapis.com/oak-index/${BINARY_FOR_COMMIT}/sha1:${commit_hash}/${package_name}")
fetch_file "${hash}" binary
```

### Step 2: Download the provenance

To download the provenance, run the following on the command line.

```bash
readonly PROV_FOR_BINARY=12
hash=$(curl "https://storage.googleapis.com/oak-index/${PROV_FOR_BINARY}/${hash}")
fetch_file "${hash}" attestation.jsonl
```

### Step 3: Find the attestation in Rekor

The GitHub workflow that generates the signed provenance shown above also
uploads it to https://rekor.sigstore.dev, which is a public instance of
[Rekor](https://github.com/sigstore/rekor) hosted by Sigstore.

The following steps describe how to fetch and examine the LogEntry in Rekor.

#### Install Rekor CLI

We are going to use `rekor-cli` for this. First, if you don't have `rekor-cli`
installed, follow
[these instructions](https://docs.sigstore.dev/rekor/installation/) to install
it.

The commands provided by `rekor-cli` allow you to specify the instance of Rekor
that you want to connect to. By default `rekor-cli` uses
https://rekor.sigstore.dev as the Rekor server. Since that is the Rekor server
we are using, in the commands below we don't explicitly specify the server.

#### Fetch and examine

The `tlogEntries` filed in the Sigstore Bundle above contains a `logIndex` that
we can pass in to `rekor-cli` to fetch the attestation information from it:

```bash
$ rekor-cli get --log-index 18196863
LogID: c0d23d6ad406973f9559f3ba2d1ca01f84147d8ffc5b8445c224f98b9591801d
Attestation: {"_type":"https://in-toto.io/Statement/v0.1","subject":[{"name":"oak_functions_enclave_app","digest":{"sha256":"813841dda3818d616aa3e706e49d0286dc825c5dbad4a75cfb37b91ba412238b"}}],"predicateType":"https://slsa.dev/provenance/v1.0?draft","predicate":{"buildDefinition":{"buildType":"https://slsa.dev/container-based-build/v0.1?draft","externalParameters":{"source":{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"f2fade6fa365ca5f9ca1159539a2ceb69e3e76f8"}},"builderImage":{"uri":"europe-west2-docker.pkg.dev/oak-ci/oak-development/oak-development@sha256:51532c757d1008bbff696d053a1d05226f6387cf232aa80b6f9c13b0759ccea0","digest":{"sha256":"51532c757d1008bbff696d053a1d05226f6387cf232aa80b6f9c13b0759ccea0"}},"configPath":"buildconfigs/oak_functions_enclave_app.toml","buildConfig":{"ArtifactPath":"./oak_functions_enclave_app/target/x86_64-unknown-none/release/oak_functions_enclave_app","Command":["env","--chdir=oak_functions_enclave_app","cargo","build","--release"]}},"resolvedDependencies":[{"uri":"git+https://github.com/slsa-framework/slsa-github-generator@refs/tags/v1.6.0-rc.0","digest":{"sha256":"b96aafbb02449d5ff041856cb0cd251ae3a895a51f10a451f5b655e0f27fc33f"}}],"systemParameters":{...}},"runDetails":{"builder":{"id":"https://github.com/slsa-framework/slsa-github-generator/.github/workflows/builder_docker-based_slsa3.yml@refs/tags/v1.6.0-rc.0"},"metadata":{"invocationId":"https://github.com/project-oak/oak/actions/runs/4723791625/attempts/1"}}}}
Index: 18196863
IntegratedTime: 2023-04-17T17:07:29Z
UUID: 24296fb24b8ad77a4c0e26d5cd66cb548d29e873b095056efd2f9d98534e1e12f7e2b64d6118b992
Body: {
  "IntotoObj": {
    "content": {
      "envelope": {
        "payloadType": "application/vnd.in-toto+json",
        "signatures": [
          {
            "publicKey": "...",
            "sig": "..."
          }
        ]
      },
      "hash": {
        "algorithm": "sha256",
        "value": "f36bd503a4c1868522d3767c1e26dcc3bea64cb281cd575e57398be32cbb2f73"
      },
      "payloadHash": {
        "algorithm": "sha256",
        "value": "cae4962ae8c477bd98e4066f8de1ceff0f512cddd082af8dbdb8417b79a8ef79"
      }
    }
  }
}
```

Note that the provenance is included in the `Attestation` field. Compared to the
Sigstore bundle above, the response in this case does not contain the
`verificationMaterial`, because `rekor-cli` already verifies the LogEntry and
its inclusion in Rekor.
