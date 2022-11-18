# Oak transparent build and release

## Per-commit build and provenance generation

Every time a pull-request is merged to `main` the binaries specified in
`.github/workflows/provenance.yaml` are built and uploaded to `ent`. Moreover,
for each binary, a
[signed SLSA3+ provenance](https://github.com/slsa-framework/slsa-github-generator/blob/04f1fe0c7b7902c9a95f4c7eef2dc04cf0f8e6a7/internal/builders/generic/README.md)
is generated and uploaded to `ent` as a
[DSSE document](https://github.com/secure-systems-lab/dsse/blob/master/protocol.md).
The signed provenances are also uploaded to the public instance of Rekor hosted
by Sigstore at https://rekor.sigstore.dev, and can be downloaded from it.

## Including a new binary in provenance generation

To include a new binary in this build and release process, a buildconfig file
must be provided, and added to the provenance generation workflow.

### Step 1: Add a new buildconfig file

A buildconfig is a `.toml` file containing three fields:

- `repo`: URI of the Oak GitHub repo (i.e.,
  "https://github.com/project-oak/oak")
- `command`: The command for building the binary that will be passed to
  `docker run`. It must be specified as an array.
- `output_path`: The path of the generated binary file, relative to the root of
  the Git repository.

The `output_path` must be the last line of the `.toml` file, so that the
provenance generation workflow can retrieve the path. For an example see
`./buildconfigs/oak_functions_freestanding_bin.toml`.

You need to add the config file to the `./buildconfigs` folder.

### Step 2: Add the buildconfig to the provenance generation workflow

The provenance generation workflow uses a matrix strategy to parameterize
provenance generation. To include a new file, you need to add the path to the
new buildconfig file to `.github/workflows/provenance.yaml` as a new value for
the matrix variable `buildconfig`:

```yaml
jobs:
  build_binary:
    # We use the same job template to generate provenances for multiple binaries.
    strategy:
      fail-fast: false
      matrix:
        buildconfig:
          - buildconfigs/oak_functions_freestanding_bin.toml
          - buildconfigs/<name_of_the_new_buildconfig_file>
```

## Retrieving a previously-built binary and its provenance

To release a binary transparently, you have to endorse it first, using the
[`endorser tool`](https://github.com/project-oak/transparent-release/tree/main/internal/endorser).
The endorser takes as input the hash of a binary and one or more provenances,
then it verifies the provenances, and generates an endorsement statement. This
section describes how to obtain the binary and its provenance to use with the
`endorser tool`. For more details on using the endorser tool see
[these instructions (currently WIP)](https://github.com/project-oak/transparent-release/tree/main/cmd).

Once you merge a pull-request to `main`, all CI steps are executed on branch
`main`, and an automated comment is added to the pull-request for each
buildconfig (and built binary). The comment contains the SHA256 digests of the
binary and its provenance. We will use these digests to download a binary and
its provenance from `ent`.

TODO: Update the following after #3473 is merged.

For instance the following are the auto-generated comments posted on
[PR #3399](https://github.com/project-oak/oak/pull/3399). The
[first comment](https://github.com/project-oak/oak/pull/3399#issuecomment-1294834494)
contains the digest of the `oak_functions_freestanding_bin` binary:

```bash
b78336fe0d0d736ae6d5ecdbce1934aa92e3c02a43ad01533bff41468c200f05  ./oak_functions_freestanding_bin/target/x86_64-unknown-none/release/oak_functions_freestanding_bin
```

The
[second comment](https://github.com/project-oak/oak/pull/3399#issuecomment-1294837399)
contains the digest of the signed provenance:

```bash
sha256:cdbabdee36d4820eb97cc2ca62c5f9668342758cfb5605c76b09d1cb4a52e1d2 ↑ [ent-store]
```

### Step 1: Download the binary

With the SHA256 digest of the binary from the first comment
(`b78336fe0d0d736ae6d5ecdbce1934aa92e3c02a43ad01533bff41468c200f05`), you can
download the binary from `ent`, with the following command using the
[ent HTTP API](https://github.com/google/ent#raw-http-api):

```bash
$ curl --output oak_functions_freestanding_bin_from_ent  https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha256:b78336fe0d0d736ae6d5ecdbce1934aa92e3c02a43ad01533bff41468c200f05
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 2340k    0 2340k    0     0  1263k      0 --:--:--  0:00:01 --:--:-- 1263k
```

### Step 2: Download the signed provenance

Similarly, you can use the SHA256 digest of the provenance from the second
comment to download the provenance from `ent`:

```bash
$ curl --output oak_functions_freestanding_provenance.jsonl  https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha256:cdbabdee36d4820eb97cc2ca62c5f9668342758cfb5605c76b09d1cb4a52e1d2
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 15150    0 15150    0     0  35777      0 --:--:-- --:--:-- --:--:-- 35900
```

The downloaded file is a DSSE document similar to the following:

```json
{
  "payloadType": "application/vnd.in-toto+json",
  "payload": "<base64-encoded provenance>",
  "signatures": [
    {
      "keyid": "",
      "sig": "MEUCIQC+EPMtG0mK8R75DR4+qkvneNKOZZ+aXZfcGF0kbmNQ0AIgDXrr7vuSp3cqfR0FAm10j81nA4amBeLJaFMyeAgo4xk=",
      "cert": "-----BEGIN CERTIFICATE-----\nMIIDvDCCA0KgAwIBAgIUNPUebYs8sHuMCFKpluSBjmuZaD8wCgYIKoZIzj0EAwMw\nNzEVMBMGA1UEChMMc2lnc3RvcmUuZGV2MR4wHAYDVQQDExVzaWdzdG9yZS1pbnRl\ncm1lZGlhdGUwHhcNMjIxMDI4MTAzODQ0WhcNMjIxMDI4MTA0ODQ0WjAAMFkwEwYH\nKoZIzj0CAQYIKoZIzj0DAQcDQgAECajzJ3reeI/WoEGEodIU5d0Ml7Nranr692Kb\n5PegQHTlni2Mhau+2k8kmgX00LnTQb/4r3H5gqSKIw+kn8faIqOCAmEwggJdMA4G\nA1UdDwEB/wQEAwIHgDATBgNVHSUEDDAKBggrBgEFBQcDAzAdBgNVHQ4EFgQURwti\nk7Q/gfNGVivunJ8TkEKi8B4wHwYDVR0jBBgwFoAU39Ppz1YkEZb5qNjpKFWixi4Y\nZD8wgYQGA1UdEQEB/wR6MHiGdmh0dHBzOi8vZ2l0aHViLmNvbS9zbHNhLWZyYW1l\nd29yay9zbHNhLWdpdGh1Yi1nZW5lcmF0b3IvLmdpdGh1Yi93b3JrZmxvd3MvZ2Vu\nZXJhdG9yX2dlbmVyaWNfc2xzYTMueW1sQHJlZnMvdGFncy92MS4yLjEwOQYKKwYB\nBAGDvzABAQQraHR0cHM6Ly90b2tlbi5hY3Rpb25zLmdpdGh1YnVzZXJjb250ZW50\nLmNvbTASBgorBgEEAYO/MAECBARwdXNoMDYGCisGAQQBg78wAQMEKDZlNGJjOGVh\nYjAzYzM5NWNlMTM1Zjk5ZDg0NGMxY2E5ZTdhMGJlMjgwHgYKKwYBBAGDvzABBAQQ\nQnVpbGQgUHJvdmVuYW5jZTAdBgorBgEEAYO/MAEFBA9wcm9qZWN0LW9hay9vYWsw\nHQYKKwYBBAGDvzABBgQPcmVmcy9oZWFkcy9tYWluMIGJBgorBgEEAdZ5AgQCBHsE\neQB3AHUACGCS8ChS/2hF0dFrJ4ScRWcYrBY9wzjSbea8IgY2b3IAAAGEHiw0FAAA\nBAMARjBEAiAfmI+rhpUIRH4BaqDcFrxpO2xFBOmc32XSRxjyINjgNwIgcEhVUt6S\n9r0X81PqlwJq67CK5h6nSOu/HMNJW0VtZo8wCgYIKoZIzj0EAwMDaAAwZQIxAJIG\n7zbfAXwbwycMamAnvEX45rjj/xPXy/f6KcDiTQL47i1juLV9jj9o1HNG6pOFaQIw\nefKBOgY1qioq70mi+5J332KpkykCQEzYREUWiqR4fcw6cFxc0i6P7RvtR4LeQD2h\n-----END CERTIFICATE-----\n"
    }
  ]
}
```

### Step 3: Download the inclusion proof from Rekor (Optional)

The GitHub workflow that generates the signed provenance also uploads it to
https://rekor.sigstore.dev, which is a public instance of
[Rekor](https://github.com/sigstore/rekor) hosted by Sigstore.

The following steps describe how to download the proof of inclusion from Rekor.
You will use the Rekor HTTP API to download the inclusion proof as a Rekor
LogEntry. But for that, you need the UUID of the LogEntry.

We are going to use `rekor-cli` to retrieve the UUID of the LogEntry
corresponding to our signed provenance. First, if you don't have `rekor-cli`,
follow [these instructions](https://docs.sigstore.dev/rekor/installation/) to
install it.

The commands provided by `rekor-cli` allow you to specify the instance of Rekor
that you want to connect to. By default `rekor-cli` uses
https://rekor.sigstore.dev as the Rekor server. Since that is the Rekor server
we are using, in the commands below we don't explicitly specify the server.

#### Find the UUID of the Rekor LogEntry using `rekor-cli`

The `rekor-cli search` command retrieves the UUIDs of all the LogEntries that
refer to a given artifact, e.g., a binary, specified by its digest. Both SHA1
and SHA256 digests are supported.

The following is the command you can use together with the SHA256 digest of the
binary from the earlier steps to retrieve the UUID of the LogEntry:

```bash
$ rekor-cli search --sha b78336fe0d0d736ae6d5ecdbce1934aa92e3c02a43ad01533bff41468c200f05
Found matching entries (listed by UUID):
24296fb24b8ad77a930a23813ed81831e97480dad2378ee84d9da23e9906e1e624ddfcde3d366835
24296fb24b8ad77adbf05f042039ff160593bd693f4414ec25d8cd79b44abd97e7bf809b5b391fc8
```

Usually there is only one entry, but it is possible to get multiple entries.

Alternatively, you can use the SHA1 Git commit hash to find the same LogEntry.
You can find the commit hash on the pull-request on GitHub.

```bash
$ rekor-cli search --sha 6e4bc8eab03c395ce135f99d844c1ca9e7a0be28
Found matching entries (listed by UUID):
24296fb24b8ad77a930a23813ed81831e97480dad2378ee84d9da23e9906e1e624ddfcde3d366835
```

#### Download the LogEntry using Rekor HTTP API

Now that you have the UUID of the Rekor LogEntry, you can use the Rekor HTTP API
to download the LogEntry:

```bash
$ curl --output signed-provenance-entry https://rekor.sigstore.dev/api/v1/log/entries/24296fb24b8ad77a930a23813ed81831e97480dad2378ee84d9da23e9906e1e624ddfcde3d366835
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 18313    0 18313    0     0  30135      0 --:--:-- --:--:-- --:--:-- 30169
```

The downloaded file is a JSON document. In addition to the inclusion proof
contained in the `verification` field, the LogEntry also contains the provenance
in the `attestation.data` field as a base64-encoded string.

If you are curious how the provenance looks like, you can extract it from the
LogEntry using the following command:

```bash
$ jq .[].attestation.data signed-provenance-entry | tr --delete '"' | base64 --decode
{"_type":"https://in-toto.io/Statement/v0.1","predicateType":"https://slsa.dev/provenance/v0.2","subject":[{"name":"oak_functions_freestanding_bin","digest":{"sha256":"b78336fe0d0d736ae6d5ecdbce1934aa92e3c02a43ad01533bff41468c200f05"}}],"predicate":{"builder":{"id":"https://github.com/slsa-framework/slsa-github-generator/.github/workflows/generator_generic_slsa3.yml@refs/tags/v1.2.1"},"buildType":"https://github.com/slsa-framework/slsa-github-generator/generic@v1","invocation":{"configSource":{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"6e4bc8eab03c395ce135f99d844c1ca9e7a0be28"},"entryPoint":".github/workflows/provenance.yaml"},"parameters":{},"environment":{ "/* GitHub context */" }},"metadata":{"buildInvocationID":"3344664625-1","completeness":{"parameters":true,"environment":false,"materials":false},"reproducible":false},"materials":[{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"6e4bc8eab03c395ce135f99d844c1ca9e7a0be28"}}]}}
```

Optional: Verify that this is the same as the provenance (i.e., payload) in the
DSSE document downloaded in step 2.

#### Optional: Explore the LogEntry using `rekor-cli`

The LogEntry downloaded in the previous step is more suitable for automated
verification and is not very human readable.

If you are interested in exploring the details of the LogEntry, you can use
`rekor-cli` with the UUID of the LogEntry to get a more human-readable version
of the LogEntry:

```bash
$ rekor-cli get --uuid 24296fb24b8ad77a930a23813ed81831e97480dad2378ee84d9da23e9906e1e624ddfcde3d366835
LogID: c0d23d6ad406973f9559f3ba2d1ca01f84147d8ffc5b8445c224f98b9591801d
Attestation: {"_type":"https://in-toto.io/Statement/v0.1","predicateType":"https://slsa.dev/provenance/v0.2","subject":[{"name":"oak_functions_freestanding_bin","digest":{"sha256":"b78336fe0d0d736ae6d5ecdbce1934aa92e3c02a43ad01533bff41468c200f05"}}],"predicate":{"builder":{"id":"https://github.com/slsa-framework/slsa-github-generator/.github/workflows/generator_generic_slsa3.yml@refs/tags/v1.2.1"},"buildType":"https://github.com/slsa-framework/slsa-github-generator/generic@v1","invocation":{"configSource":{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"6e4bc8eab03c395ce135f99d844c1ca9e7a0be28"},"entryPoint":".github/workflows/provenance.yaml"},"parameters":{},"environment":{ "/* GitHub context */" }},"metadata":{"buildInvocationID":"3344664625-1","completeness":{"parameters":true,"environment":false,"materials":false},"reproducible":false},"materials":[{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"6e4bc8eab03c395ce135f99d844c1ca9e7a0be28"}}]}}
Index: 6037020
IntegratedTime: 2022-10-28T10:38:44Z
UUID: 24296fb24b8ad77a930a23813ed81831e97480dad2378ee84d9da23e9906e1e624ddfcde3d366835
Body: {
  "IntotoObj": {
    "content": {
      "hash": {
        "algorithm": "sha256",
        "value": "cdbabdee36d4820eb97cc2ca62c5f9668342758cfb5605c76b09d1cb4a52e1d2"
      },
      "payloadHash": {
        "algorithm": "sha256",
        "value": "2b0e53da53bbf1bc2405e724f3f99c756a72f314966a38cebac469c397ea51d7"
      }
    },
    "publicKey": "LS0tLS1CRUdJTiBDRVJUSUZJQ0FURS0tLS0tCk1JSUR2RENDQTBLZ0F3SUJBZ0lVTlBVZWJZczhzSHVNQ0ZLcGx1U0JqbXVaYUQ4d0NnWUlLb1pJemowRUF3TXcKTnpFVk1CTUdBMVVFQ2hNTWMybG5jM1J2Y21VdVpHVjJNUjR3SEFZRFZRUURFeFZ6YVdkemRHOXlaUzFwYm5SbApjbTFsWkdsaGRHVXdIaGNOTWpJeE1ESTRNVEF6T0RRMFdoY05Nakl4TURJNE1UQTBPRFEwV2pBQU1Ga3dFd1lICktvWkl6ajBDQVFZSUtvWkl6ajBEQVFjRFFnQUVDYWp6SjNyZWVJL1dvRUdFb2RJVTVkME1sN05yYW5yNjkyS2IKNVBlZ1FIVGxuaTJNaGF1KzJrOGttZ1gwMExuVFFiLzRyM0g1Z3FTS0l3K2tuOGZhSXFPQ0FtRXdnZ0pkTUE0RwpBMVVkRHdFQi93UUVBd0lIZ0RBVEJnTlZIU1VFRERBS0JnZ3JCZ0VGQlFjREF6QWRCZ05WSFE0RUZnUVVSd3RpCms3US9nZk5HVml2dW5KOFRrRUtpOEI0d0h3WURWUjBqQkJnd0ZvQVUzOVBwejFZa0VaYjVxTmpwS0ZXaXhpNFkKWkQ4d2dZUUdBMVVkRVFFQi93UjZNSGlHZG1oMGRIQnpPaTh2WjJsMGFIVmlMbU52YlM5emJITmhMV1p5WVcxbApkMjl5YXk5emJITmhMV2RwZEdoMVlpMW5aVzVsY21GMGIzSXZMbWRwZEdoMVlpOTNiM0pyWm14dmQzTXZaMlZ1ClpYSmhkRzl5WDJkbGJtVnlhV05mYzJ4ellUTXVlVzFzUUhKbFpuTXZkR0ZuY3k5Mk1TNHlMakV3T1FZS0t3WUIKQkFHRHZ6QUJBUVFyYUhSMGNITTZMeTkwYjJ0bGJpNWhZM1JwYjI1ekxtZHBkR2gxWW5WelpYSmpiMjUwWlc1MApMbU52YlRBU0Jnb3JCZ0VFQVlPL01BRUNCQVJ3ZFhOb01EWUdDaXNHQVFRQmc3OHdBUU1FS0RabE5HSmpPR1ZoCllqQXpZek01TldObE1UTTFaams1WkRnME5HTXhZMkU1WlRkaE1HSmxNamd3SGdZS0t3WUJCQUdEdnpBQkJBUVEKUW5WcGJHUWdVSEp2ZG1WdVlXNWpaVEFkQmdvckJnRUVBWU8vTUFFRkJBOXdjbTlxWldOMExXOWhheTl2WVdzdwpIUVlLS3dZQkJBR0R2ekFCQmdRUGNtVm1jeTlvWldGa2N5OXRZV2x1TUlHSkJnb3JCZ0VFQWRaNUFnUUNCSHNFCmVRQjNBSFVBQ0dDUzhDaFMvMmhGMGRGcko0U2NSV2NZckJZOXd6alNiZWE4SWdZMmIzSUFBQUdFSGl3MEZBQUEKQkFNQVJqQkVBaUFmbUkrcmhwVUlSSDRCYXFEY0ZyeHBPMnhGQk9tYzMyWFNSeGp5SU5qZ053SWdjRWhWVXQ2Uwo5cjBYODFQcWx3SnE2N0NLNWg2blNPdS9ITU5KVzBWdFpvOHdDZ1lJS29aSXpqMEVBd01EYUFBd1pRSXhBSklHCjd6YmZBWHdid3ljTWFtQW52RVg0NXJqai94UFh5L2Y2S2NEaVRRTDQ3aTFqdUxWOWpqOW8xSE5HNnBPRmFRSXcKZWZLQk9nWTFxaW9xNzBtaSs1SjMzMktwa3lrQ1FFellSRVVXaXFSNGZjdzZjRnhjMGk2UDdSdnRSNExlUUQyaAotLS0tLUVORCBDRVJUSUZJQ0FURS0tLS0tCg=="
  }
}
```

In this case, the provenance is in the `Attestation` field. The response in this
case does not contain the verification, because `rekor-cli` already verifies the
LogEntry and its inclusion in Rekor. However, it contains other details,
including the `Body.IntotoObj` object. The `payloadHash` in this object is the
SHA256 hash of the provenance.
