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

For instance the following is the
[auto-generated comment](https://github.com/project-oak/oak/pull/3473#issuecomment-1320306415)
posted on [PR #3473](https://github.com/project-oak/oak/pull/3473).

```bash

Artifact digest and name:

ccf7bc7d07dc7f74dffa5485dc795e90bb1deec27286c65debca878226eeb16a  oak_functions_freestanding_bin

Provenance digest:

sha256:729291baba0ec2bb6eff7528e8aa0d0dd1fbfaccd3c59219174b182fe1f8e5ff ↑ [ent-store]
```

The comment contains the SHA256 digest of the binary
(`oak_functions_freestanding_bin`):

```text
ccf7bc7d07dc7f74dffa5485dc795e90bb1deec27286c65debca878226eeb16a
```

and the digest of the signed provenance generated for the binary:

```text
sha256:729291baba0ec2bb6eff7528e8aa0d0dd1fbfaccd3c59219174b182fe1f8e5ff
```

### Step 1: Download the binary

With the SHA256 digest of the binary
(`ccf7bc7d07dc7f74dffa5485dc795e90bb1deec27286c65debca878226eeb16a`), you can
download the binary from `ent`, with the following command using the
[ent HTTP API](https://github.com/google/ent#raw-http-api):

```bash
$ curl --output oak_functions_freestanding_bin_from_ent  https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha256:ccf7bc7d07dc7f74dffa5485dc795e90bb1deec27286c65debca878226eeb16a
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 2298k    0 2298k    0     0  3541k      0 --:--:-- --:--:-- --:--:-- 3541k
```

### Step 2: Download the signed provenance

Similarly, you can use the SHA256 digest of the provenance to download the
provenance from `ent`:

```bash
$ curl --output oak_functions_freestanding_provenance.jsonl  https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha256:729291baba0ec2bb6eff7528e8aa0d0dd1fbfaccd3c59219174b182fe1f8e5ff
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 14548    0 14548    0     0  33443      0 --:--:-- --:--:-- --:--:-- 33443
```

The downloaded file is a DSSE document similar to the following:

```json
{
  "payloadType": "application/vnd.in-toto+json",
  "payload": "<base64-encoded provenance>",
  "signatures": [
    {
      "keyid": "",
      "sig": "MEYCIQCc1e4EXohTqYrIQbaKCm8we5gPO+3pmVIeeThY+qNC9wIhANFgNrLDuzKGy3+YxiRfUbNN/CxeDkmSIcz4Qk2ILbdL",
      "cert": "-----BEGIN CERTIFICATE-----\nMIIDwTCCA0egAwIBAgIUccFLTQVvODK/jdhVS+Osx5ACYuUwCgYIKoZIzj0EAwMw\nNzEVMBMGA1UEChMMc2lnc3RvcmUuZGV2MR4wHAYDVQQDExVzaWdzdG9yZS1pbnRl\ncm1lZGlhdGUwHhcNMjIxMTE4MTcxNjIxWhcNMjIxMTE4MTcyNjIxWjAAMFkwEwYH\nKoZIzj0CAQYIKoZIzj0DAQcDQgAEDM4CDZI1aXFFjBg5wLZITyV0tFIE/uQ6Z9qr\n4Y0FPhiktSxPo4pX2x/cUV8224zZ9Z16ZQKRCDOsKHup9njRqKOCAmYwggJiMA4G\nA1UdDwEB/wQEAwIHgDATBgNVHSUEDDAKBggrBgEFBQcDAzAdBgNVHQ4EFgQUWui+\n2jN0g/mZcPTk8i9l+dF9yzswHwYDVR0jBBgwFoAU39Ppz1YkEZb5qNjpKFWixi4Y\nZD8wgYQGA1UdEQEB/wR6MHiGdmh0dHBzOi8vZ2l0aHViLmNvbS9zbHNhLWZyYW1l\nd29yay9zbHNhLWdpdGh1Yi1nZW5lcmF0b3IvLmdpdGh1Yi93b3JrZmxvd3MvZ2Vu\nZXJhdG9yX2dlbmVyaWNfc2xzYTMueW1sQHJlZnMvdGFncy92MS4yLjEwOQYKKwYB\nBAGDvzABAQQraHR0cHM6Ly90b2tlbi5hY3Rpb25zLmdpdGh1YnVzZXJjb250ZW50\nLmNvbTASBgorBgEEAYO/MAECBARwdXNoMDYGCisGAQQBg78wAQMEKDM5ODEwNDdk\nYjhmOWY2MTM1NWFiOTMwNTRmYTAzOWM5MDcwOTRjYzUwIwYKKwYBBAGDvzABBAQV\nQnVpbGQgQWxsIFByb3ZlbmFuY2VzMB0GCisGAQQBg78wAQUED3Byb2plY3Qtb2Fr\nL29hazAdBgorBgEEAYO/MAEGBA9yZWZzL2hlYWRzL21haW4wgYkGCisGAQQB1nkC\nBAIEewR5AHcAdQDdPTBqxscRMmMZHhyZZzcCokpeuN48rf+HinKALynujgAAAYSL\nvcnfAAAEAwBGMEQCIBvMe9yLyRdVN7vm7L4rR9Cf83TjhsoFSnJl/Iq9gVKlAiB+\nqYu+C05lLt428acwDQCqylgC/VRO1kCi6amKpTiW3DAKBggqhkjOPQQDAwNoADBl\nAjEAm+7l/o3H0YWEK/3Wx3dWVVQaMGSAQt/n+qRRgEdbknriu06SmAcOr+pjezGh\n2lbtAjAQxnun57zv3K6E1DI2tH5qI5S0YBN42gkiPi9ioEz85O+rve5zF9/Nmsch\nTKTaxCw=\n-----END CERTIFICATE-----\n"
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
$ rekor-cli search --sha ccf7bc7d07dc7f74dffa5485dc795e90bb1deec27286c65debca878226eeb16a
Found matching entries (listed by UUID):
24296fb24b8ad77aefea290b5d85e9487fbfbac8a2a03e2f315818088b6868160a9c6e6219ccbf2c
24296fb24b8ad77a80749c88e748a38199301c06daba6eeb4e242dcc5839fc45c7b52de6f40d1cb4
```

Usually there is only one entry, but it is possible to get multiple entries.

Alternatively, you can use the SHA1 Git commit hash to find the same LogEntry.
You can find the commit hash on the pull-request on GitHub.

```bash
$ rekor-cli search --sha 3981047db8f9f61355ab93054fa039c907094cc5
Found matching entries (listed by UUID):
24296fb24b8ad77a80749c88e748a38199301c06daba6eeb4e242dcc5839fc45c7b52de6f40d1cb4
```

#### Download the LogEntry using Rekor HTTP API

Now that you have the UUID of the Rekor LogEntry, you can use the Rekor HTTP API
to download the LogEntry:

```bash
$ curl --output signed-provenance-entry https://rekor.sigstore.dev/api/v1/log/entries/24296fb24b8ad77a80749c88e748a38199301c06daba6eeb4e242dcc5839fc45c7b52de6f40d1cb4
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 17654    0 17654    0     0  27763      0 --:--:-- --:--:-- --:--:-- 27757
```

The downloaded file is a JSON document. In addition to the inclusion proof
contained in the `verification` field, the LogEntry also contains the provenance
in the `attestation.data` field as a base64-encoded string.

If you are curious how the provenance looks like, you can extract it from the
LogEntry using the following command:

```bash
$ jq .[].attestation.data signed-provenance-entry | tr --delete '"' | base64 --decode
{"_type":"https://in-toto.io/Statement/v0.1","predicateType":"https://slsa.dev/provenance/v0.2","subject":[{"name":"oak_functions_freestanding_bin","digest":{"sha256":"ccf7bc7d07dc7f74dffa5485dc795e90bb1deec27286c65debca878226eeb16a"}}],"predicate":{"builder":{"id":"https://github.com/slsa-framework/slsa-github-generator/.github/workflows/generator_generic_slsa3.yml@refs/tags/v1.2.1"},"buildType":"https://github.com/slsa-framework/slsa-github-generator/generic@v1","invocation":{"configSource":{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"3981047db8f9f61355ab93054fa039c907094cc5"},"entryPoint":".github/workflows/provenance.yaml"},"parameters":{},"environment":{"/* GitHub context */"}},"metadata":{"buildInvocationID":"3498762287-1","completeness":{"parameters":true,"environment":false,"materials":false},"reproducible":false},"materials":[{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"3981047db8f9f61355ab93054fa039c907094cc5"}}]}}
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
$ $ rekor-cli get --uuid 24296fb24b8ad77a80749c88e748a38199301c06daba6eeb4e242dcc5839fc45c7b52de6f40d1cb4
LogID: c0d23d6ad406973f9559f3ba2d1ca01f84147d8ffc5b8445c224f98b9591801d
Attestation: {"_type":"https://in-toto.io/Statement/v0.1","predicateType":"https://slsa.dev/provenance/v0.2","subject":[{"name":"oak_functions_freestanding_bin","digest":{"sha256":"ccf7bc7d07dc7f74dffa5485dc795e90bb1deec27286c65debca878226eeb16a"}}],"predicate":{"builder":{"id":"https://github.com/slsa-framework/slsa-github-generator/.github/workflows/generator_generic_slsa3.yml@refs/tags/v1.2.1"},"buildType":"https://github.com/slsa-framework/slsa-github-generator/generic@v1","invocation":{"configSource":{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"3981047db8f9f61355ab93054fa039c907094cc5"},"entryPoint":".github/workflows/provenance.yaml"},"parameters":{},"environment":{"/* GitHub context */"}},"metadata":{"buildInvocationID":"3498762287-1","completeness":{"parameters":true,"environment":false,"materials":false},"reproducible":false},"materials":[{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"3981047db8f9f61355ab93054fa039c907094cc5"}}]}}
Index: 7359481
IntegratedTime: 2022-11-18T17:16:22Z
UUID: 24296fb24b8ad77a80749c88e748a38199301c06daba6eeb4e242dcc5839fc45c7b52de6f40d1cb4
Body: {
  "IntotoObj": {
    "content": {
      "hash": {
        "algorithm": "sha256",
        "value": "729291baba0ec2bb6eff7528e8aa0d0dd1fbfaccd3c59219174b182fe1f8e5ff"
      },
      "payloadHash": {
        "algorithm": "sha256",
        "value": "92139853842fa8cc1a82f463f35f976f57e5b0f828f7fc968b1dcdd12b0b6355"
      }
    },
    "publicKey": "LS0tLS1CRUdJTiBDRVJUSUZJQ0FURS0tLS0tCk1JSUR3VENDQTBlZ0F3SUJBZ0lVY2NGTFRRVnZPREsvamRoVlMrT3N4NUFDWXVVd0NnWUlLb1pJemowRUF3TXcKTnpFVk1CTUdBMVVFQ2hNTWMybG5jM1J2Y21VdVpHVjJNUjR3SEFZRFZRUURFeFZ6YVdkemRHOXlaUzFwYm5SbApjbTFsWkdsaGRHVXdIaGNOTWpJeE1URTRNVGN4TmpJeFdoY05Nakl4TVRFNE1UY3lOakl4V2pBQU1Ga3dFd1lICktvWkl6ajBDQVFZSUtvWkl6ajBEQVFjRFFnQUVETTRDRFpJMWFYRkZqQmc1d0xaSVR5VjB0RklFL3VRNlo5cXIKNFkwRlBoaWt0U3hQbzRwWDJ4L2NVVjgyMjR6WjlaMTZaUUtSQ0RPc0tIdXA5bmpScUtPQ0FtWXdnZ0ppTUE0RwpBMVVkRHdFQi93UUVBd0lIZ0RBVEJnTlZIU1VFRERBS0JnZ3JCZ0VGQlFjREF6QWRCZ05WSFE0RUZnUVVXdWkrCjJqTjBnL21aY1BUazhpOWwrZEY5eXpzd0h3WURWUjBqQkJnd0ZvQVUzOVBwejFZa0VaYjVxTmpwS0ZXaXhpNFkKWkQ4d2dZUUdBMVVkRVFFQi93UjZNSGlHZG1oMGRIQnpPaTh2WjJsMGFIVmlMbU52YlM5emJITmhMV1p5WVcxbApkMjl5YXk5emJITmhMV2RwZEdoMVlpMW5aVzVsY21GMGIzSXZMbWRwZEdoMVlpOTNiM0pyWm14dmQzTXZaMlZ1ClpYSmhkRzl5WDJkbGJtVnlhV05mYzJ4ellUTXVlVzFzUUhKbFpuTXZkR0ZuY3k5Mk1TNHlMakV3T1FZS0t3WUIKQkFHRHZ6QUJBUVFyYUhSMGNITTZMeTkwYjJ0bGJpNWhZM1JwYjI1ekxtZHBkR2gxWW5WelpYSmpiMjUwWlc1MApMbU52YlRBU0Jnb3JCZ0VFQVlPL01BRUNCQVJ3ZFhOb01EWUdDaXNHQVFRQmc3OHdBUU1FS0RNNU9ERXdORGRrCllqaG1PV1kyTVRNMU5XRmlPVE13TlRSbVlUQXpPV001TURjd09UUmpZelV3SXdZS0t3WUJCQUdEdnpBQkJBUVYKUW5WcGJHUWdRV3hzSUZCeWIzWmxibUZ1WTJWek1CMEdDaXNHQVFRQmc3OHdBUVVFRDNCeWIycGxZM1F0YjJGcgpMMjloYXpBZEJnb3JCZ0VFQVlPL01BRUdCQTl5WldaekwyaGxZV1J6TDIxaGFXNHdnWWtHQ2lzR0FRUUIxbmtDCkJBSUVld1I1QUhjQWRRRGRQVEJxeHNjUk1tTVpIaHlaWnpjQ29rcGV1TjQ4cmYrSGluS0FMeW51amdBQUFZU0wKdmNuZkFBQUVBd0JHTUVRQ0lCdk1lOXlMeVJkVk43dm03TDRyUjlDZjgzVGpoc29GU25KbC9JcTlnVktsQWlCKwpxWXUrQzA1bEx0NDI4YWN3RFFDcXlsZ0MvVlJPMWtDaTZhbUtwVGlXM0RBS0JnZ3Foa2pPUFFRREF3Tm9BREJsCkFqRUFtKzdsL28zSDBZV0VLLzNXeDNkV1ZWUWFNR1NBUXQvbitxUlJnRWRia25yaXUwNlNtQWNPcitwamV6R2gKMmxidEFqQVF4bnVuNTd6djNLNkUxREkydEg1cUk1UzBZQk40MmdraVBpOWlvRXo4NU8rcnZlNXpGOS9ObXNjaApUS1RheEN3PQotLS0tLUVORCBDRVJUSUZJQ0FURS0tLS0tCg=="
  }
}
```

In this case, the provenance is in the `Attestation` field. The response in this
case does not contain the verification, because `rekor-cli` already verifies the
LogEntry and its inclusion in Rekor. However, it contains other details,
including the `Body.IntotoObj` object. The `payloadHash` in this object is the
SHA256 hash of the provenance.
