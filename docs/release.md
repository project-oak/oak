# Oak transparent build and release

## Per-commit build and provenance generation

Every time a pull-request is merged to `main` the binaries specified in
[/.github/workflows/provenance.yaml](/.github/workflows/provenance.yaml) are
built and uploaded to `ent`. Moreover, for each binary, a
[signed SLSA3+ provenance](https://github.com/slsa-framework/slsa-github-generator/blob/04f1fe0c7b7902c9a95f4c7eef2dc04cf0f8e6a7/internal/builders/generic/README.md)
is generated and uploaded to `ent` as a
[DSSE document](https://github.com/secure-systems-lab/dsse/blob/master/protocol.md),
stored in a
[Sigstore Bundle](https://github.com/sigstore/protobuf-specs/blob/b6d25769ec1d565ba45fd121310daf4ab963da9b/protos/sigstore_bundle.proto#L80).
The signed provenances are also uploaded to the public instance of Rekor hosted
by Sigstore at https://rekor.sigstore.dev, and can be downloaded from it.

## Including a new binary in provenance generation

To include a new binary in this build and release process, a buildconfig file
must be provided, and added to the provenance generation workflow.

### Step 1: Add a new buildconfig file

A buildconfig is a `.toml` file containing the following fields:

- `command`: The command for building the binary that will be passed to
  `docker run`. It must be specified as an array.
- `artifact_path`: The path of the generated binary file, relative to the root
  of the Git repository.

The `artifact_path` must be the last line of the `.toml` file, so that the
provenance generation workflow can retrieve the path. For an example see
[/buildconfigs/oak_functions_enclave_app.toml](/buildconfigs/oak_functions_enclave_app.toml).

You need to add the config file to the [/buildconfigs](/buildconfigs) folder.

### Step 2: Add the buildconfig to the provenance generation workflow

The provenance generation workflow uses a matrix strategy to parameterize
provenance generation. To include a new file, you need to add the path of the
new buildconfig file to
[/.github/workflows/provenance.yaml](/.github/workflows/provenance.yaml) as a
new value for the matrix variable `buildconfig`:

```yaml
jobs:
  build_binary:
    # We use the same job template to generate provenances for multiple binaries.
    strategy:
      fail-fast: false
      matrix:
        buildconfig:
          - buildconfigs/oak_functions_enclave_app.toml
          - buildconfigs/<name_of_the_new_buildconfig_file>
```

## Retrieving a previously-built binary and its provenance (Optional)

With this configuration, every time a pull-request is merged into branch `main`,
the provenance workflow is executed on branch `main`. For each of the
buildconfigs, the workflow first builds the binary using the given command, and
then generates and signs a SLSA v1.0 provenance for the binary. Then an
automated comment is published on the pull-request containing the SHA256 digests
of the binary and its provenance. You can use these digests to download and use
or inspect a binary and its provenance from `ent`.

For instance the following is an
[auto-generated comment](https://github.com/project-oak/oak/pull/3874#issuecomment-1511760425)
posted on [PR #3874](https://github.com/project-oak/oak/pull/3874).

```bash
Artifact name: oak_functions_enclave_app
Artifact digest:

sha256:813841dda3818d616aa3e706e49d0286dc825c5dbad4a75cfb37b91ba412238b ↑ [ent-store]


Provenance digest:

sha256:8850ac28993e71b9d8e93a71557a065dd952b3ffc2b8e48d8d7d500471cf9ea3 ↑ [ent-store]
```

The comment contains the digest of the binary (`oak_functions_enclave_app`):

```text
sha256:813841dda3818d616aa3e706e49d0286dc825c5dbad4a75cfb37b91ba412238b
```

and the digest of the signed provenance generated for the binary:

```text
sha256:8850ac28993e71b9d8e93a71557a065dd952b3ffc2b8e48d8d7d500471cf9ea3
```

The following steps describe how you can use this information to download the
binary, and download and inspect its provenance.

### Step 1: Download the binary

With the SHA256 digest of the binary
(`813841dda3818d616aa3e706e49d0286dc825c5dbad4a75cfb37b91ba412238b`), you can
download the binary from `ent`, with the following command using the
[ent HTTP API](https://github.com/google/ent#raw-http-api):

```bash
$ curl --output oak_functions_enclave_app_from_ent  https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha256:813841dda3818d616aa3e706e49d0286dc825c5dbad4a75cfb37b91ba412238b
 % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 2209k    0 2209k    0     0  3371k      0 --:--:-- --:--:-- --:--:-- 3378k
```

### Step 2: Download the signed provenance

Similarly, you can use the SHA256 digest of the provenance to download the
provenance from `ent`:

```bash
$ curl --output oak_functions_enclave_app_provenance.intoto.sigstore  https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha256:8850ac28993e71b9d8e93a71557a065dd952b3ffc2b8e48d8d7d500471cf9ea3
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 23502    0 23502    0     0  56788      0 --:--:-- --:--:-- --:--:-- 56905
```

The downloaded file is a Sigstore Bundle similar to the following:

```json
{
  "mediaType": "application/vnd.dev.sigstore.bundle+json;version=0.1",
  "verificationMaterial": {
    "x509CertificateChain": {
      "certificates": [
        {
          "rawBytes": "..."
        },
        {
          "rawBytes": "..."
        },
        {
          "rawBytes": "..."
        }
      ]
    },
    "tlogEntries": [
      {
        "logIndex": "18196863",
        "logId": {
          "keyId": "wNI9atQGlz+VWfO6LRygH4QUfY/8W4RFwiT5i5WRgB0="
        },
        "kindVersion": {
          "kind": "intoto",
          "version": "0.0.2"
        },
        "integratedTime": "1681751249",
        "inclusionPromise": {
          "signedEntryTimestamp": "..."
        },
        "canonicalizedBody": "..."
      }
    ]
  },
  "dsseEnvelope": {
    "payload": "<base64-encoded provenance>",
    "payloadType": "application/vnd.in-toto+json",
    "signatures": [
      {
        "sig": "MEYCIQDwt2eTRIk6DLEBUJYLqb5iKDMHUASelusEk3XoG8pWDgIhALNiQulBbo6Upxd1vEHmz33G9+lwZW34NLXowOEaxHuH",
        "keyid": ""
      }
    ]
  }
}
```

### Step 3: Find the Attestation in Rekor

The GitHub workflow that generates the signed provenance shown above also
uploads it to https://rekor.sigstore.dev, which is a public instance of
[Rekor](https://github.com/sigstore/rekor) hosted by Sigstore.

The following steps describe how to fetch and examine the LogEntry in Rekor.

#### Using `rekor-cli`

We are going to use `rekor-cli` for this. First, if you don't have `rekor-cli`
installed, follow
[these instructions](https://docs.sigstore.dev/rekor/installation/) to install
it.

The commands provided by `rekor-cli` allow you to specify the instance of Rekor
that you want to connect to. By default `rekor-cli` uses
https://rekor.sigstore.dev as the Rekor server. Since that is the Rekor server
we are using, in the commands below we don't explicitly specify the server.

#### Explore the LogEntry using `rekor-cli`

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

## What is next?

Once the team is ready to transparently release a binary, they have to endorse
it, using the
[`endorser tool`](https://github.com/project-oak/transparent-release/tree/main/internal/endorser).
This tool takes as input the hash of a binary and one or more provenances, then
it verifies the provenances, and generates an endorsement statement.
