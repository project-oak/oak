# Oak transparent build and release

## Per-commit build and provenance generation

Every time a pull-request is merged to `main` the
`oak_functions_freestanding_bin` binary is built and uploaded to `ent`.
Similarly, a
[signed SLSA3+ provenance](https://github.com/slsa-framework/slsa-github-generator/blob/04f1fe0c7b7902c9a95f4c7eef2dc04cf0f8e6a7/internal/builders/generic/README.md)
is generated for it and uploaded to GitHub. The signed provenance is also
uploaded to the public instance of Rekor hosted by Sigstore at
https://rekor.sigstore.dev, and can be downloaded from it.

## Retrieving a previously-built binary and its provenance

To release a binary transparently, you have to endorse it first, using the
`endorser tool` (currently WIP). The endorser takes as input the hash of a
binary and one or more provenances, then it verifies the provenances, and
generates an endorsement statement. This section describes how to obtain the
binary and its provenance to use with the `endorser tool`. For more details on
using the endorser tool see
[these instructions (currently WIP)](https://github.com/project-oak/transparent-release/tree/main/cmd).

Once you merge a pull-request to `main`, all CI steps are executed on branch
`main`, and an automated comment is added to the pull-request containing the
hash of the `oak_functions_freestanding_bin` binary. For instance, the following
is the auto-generated
[comment posted on PR #3311](https://github.com/project-oak/oak/pull/3311#issuecomment-1275277376):

```bash
d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc  ./oak_functions_freestanding_bin/target/x86_64-unknown-none/release/oak_functions_freestanding_bin
```

### Step 1: Download the binary

With the hash of the binary from the comment
(`d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc`), you can
download the binary from `ent`, with the following command using the
[ent HTTP API](https://github.com/google/ent#raw-http-api):

```bash
$ curl --output oak_functions_from_ent  https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha256:d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 2327k    0 2327k    0     0  3637k      0 --:--:-- --:--:-- --:--:-- 3636k
```

### Step 2: Download the signed provenance

You can download the signed provenance, as a
[DSSE document](https://github.com/secure-systems-lab/dsse/blob/master/protocol.md),
from the GitHub actions workflow that generated the binary and its provenance
(i.e., the
[Build Provenance](https://github.com/project-oak/oak/actions/workflows/provenance.yaml)
workflow).

You need to follow the steps below:

- On github.com, navigate to the main page of the repository. Under the
  repository name, click Actions. For `oak`, this brings you to
  https://github.com/project-oak/oak/actions.
- In the left sidebar, click "Build Provenance".
- Under "Workflow runs", click the name of the run associated with your merged
  pull-request. It may help to filter the "Workflow runs" by Branch and Actor
  (i.e., you have to choose "main" as the Branch name and yourself as the
  Actor).
- At the bottom of the page (e.g.,
  [example](https://github.com/project-oak/oak/actions/runs/3230206088)), you
  can see the list of uploaded artifacts. The signed provenance for
  `oak_functions_freestanding_bin` is stored under the name
  `oak_functions_freestanding_bin.intoto.jsonl`. You can download this file as
  long as it is not expired.

TODO(#3333): We plan to upload the DSSE document to `ent` to be able to keep it
permanently. Update the instructions once the workflow is updated.

The following is how the downloaded DSSE document looks like:

```json
{
  "payloadType": "application/vnd.in-toto+json",
  "payload": "<base64-encoded provenance>",
  "signatures": [
    {
      "keyid": "",
      "sig": "MEUCIQCBAUFYTJV6K6/nvCszhYwScOrkHHSaLrqQYzuWM5BGBwIgbmwnn7iVxEM2nEK87mSLxovXuSnKqtZ9Vdk7fn5IGrY=",
      "cert": "-----BEGIN CERTIFICATE-----\nMIIDvTCCA0OgAwIBAgIUbYxISaXl3PtnznMvAqVxAEwwEyMwCgYIKoZIzj0EAwMw\nNzEVMBMGA1UEChMMc2lnc3RvcmUuZGV2MR4wHAYDVQQDExVzaWdzdG9yZS1pbnRl\ncm1lZGlhdGUwHhcNMjIxMDEyMTM0NjU5WhcNMjIxMDEyMTM1NjU5WjAAMFkwEwYH\nKoZIzj0CAQYIKoZIzj0DAQcDQgAEFk0sopU9+056g0+AwC0ZSfLLkezYQdJo066J\n4zwISwhTzWhLWCTBIop+IklTOl7rA4EL607Q8KYcUJ9JYyrAJ6OCAmIwggJeMA4G\nA1UdDwEB/wQEAwIHgDATBgNVHSUEDDAKBggrBgEFBQcDAzAdBgNVHQ4EFgQUfnSL\nzXKuuwyGguvltiSECavHt0wwHwYDVR0jBBgwFoAU39Ppz1YkEZb5qNjpKFWixi4Y\nZD8wgYQGA1UdEQEB/wR6MHiGdmh0dHBzOi8vZ2l0aHViLmNvbS9zbHNhLWZyYW1l\nd29yay9zbHNhLWdpdGh1Yi1nZW5lcmF0b3IvLmdpdGh1Yi93b3JrZmxvd3MvZ2Vu\nZXJhdG9yX2dlbmVyaWNfc2xzYTMueW1sQHJlZnMvdGFncy92MS4yLjAwOQYKKwYB\nBAGDvzABAQQraHR0cHM6Ly90b2tlbi5hY3Rpb25zLmdpdGh1YnVzZXJjb250ZW50\nLmNvbTASBgorBgEEAYO/MAECBARwdXNoMDYGCisGAQQBg78wAQMEKGEzN2FmMGVl\nM2E4MDZhNDYyZThmN2Q1NzkyMTFhMTNiZTE3OGIyOGQwHgYKKwYBBAGDvzABBAQQ\nQnVpbGQgUHJvdmVuYW5jZTAdBgorBgEEAYO/MAEFBA9wcm9qZWN0LW9hay9vYWsw\nHQYKKwYBBAGDvzABBgQPcmVmcy9oZWFkcy9tYWluMIGKBgorBgEEAdZ5AgQCBHwE\negB4AHYACGCS8ChS/2hF0dFrJ4ScRWcYrBY9wzjSbea8IgY2b3IAAAGDzHLNvwAA\nBAMARzBFAiAuNExKS7cP5J8N2sP318EXCUTz/zq0zoXZHqDaSvIM1AIhALzcaTG8\npIXPRBfPRr0J5J7EO+HTCgaAZsXbiUjOOs5iMAoGCCqGSM49BAMDA2gAMGUCMQD6\nqMASnc6IeBiiGbAFjdchyhCxCHunb+ZeLdlIu95QKKKOSGy/eTuu5B06V/1gk1sC\nMHCw+W4BrkqRIw4CvCpjdtVyv1KUplmysXHs2jQ+ATokAccs4o4DRHUn5AFq2FR6\nbA==\n-----END CERTIFICATE-----\n"
    }
  ]
}
```

### Step 3: Download the inclusion proof from Rekor

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
refer to a given artifact, e.g., a binary, specified by its hash. Both SHA1 and
SHA256 hashes are supported.

The following is the command you can use together with the SHA256 hash of the
binary from the earlier steps to retrieve the UUID of the LogEntry:

```bash
$ rekor-cli search --sha d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc
Found matching entries (listed by UUID):
24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
```

Usually there is only one entry, but it is possible to get multiple entries.

Alternatively, you can use the SHA1 Git commit hash to find the same LogEntry.
You can find the commit hash on the pull-request on GitHub.

```bash
$ rekor-cli search --sha 1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6
Found matching entries (listed by UUID):
24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
```

#### Download the LogEntry using Rekor HTTP API

Now that you have the UUID of the Rekor LogEntry, you can use the Rekor HTTP API
to download the LogEntry:

```bash
$ curl --output signed-provenance-entry https://rekor.sigstore.dev/api/v1/log/entries/24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 17907    0 17907    0     0  21765      0 --:--:-- --:--:-- --:--:-- 21758
```

The downloaded file is a JSON document. In addition to the inclusion proof
contained in the `verification` field, the LogEntry also contains the provenance
in the `attestation.data` field as a base64-encoded string.

If you are curious how the provenance looks like, you can extract it from the
LogEntry using the following command:

```bash
$ jq .[].attestation.data signed-provenance-entry | tr --delete '"' | base64 --decode
{"_type":"https://in-toto.io/Statement/v0.1","predicateType":"https://slsa.dev/provenance/v0.2","subject":[{"name":"oak_functions_freestanding_bin","digest":{"sha256":"d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc"}}],"predicate":{"builder":{"id":"https://github.com/slsa-framework/slsa-github-generator/.github/workflows/generator_generic_slsa3.yml@refs/tags/v1.2.0"},"buildType":"https://github.com/slsa-framework/slsa-github-generator@v1","invocation":{"configSource":{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6"},"entryPoint":".github/workflows/provenance.yaml"},"parameters":{},"environment":{ "/* GitHub context */"}},"metadata":{"buildInvocationID":"3230206088-1","completeness":{"parameters":true,"environment":false,"materials":false},"reproducible":false},"materials":[{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6"}}]}}
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
$ rekor-cli get --uuid 24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
LogID: c0d23d6ad406973f9559f3ba2d1ca01f84147d8ffc5b8445c224f98b9591801d
Attestation: {"_type":"https://in-toto.io/Statement/v0.1","predicateType":"https://slsa.dev/provenance/v0.2","subject":[{"name":"oak_functions_freestanding_bin","digest":{"sha256":"d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc"}}],"predicate":{"builder":{"id":"https://github.com/slsa-framework/slsa-github-generator/.github/workflows/generator_generic_slsa3.yml@refs/tags/v1.2.0"},"buildType":"https://github.com/slsa-framework/slsa-github-generator@v1","invocation":{"configSource":{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6"},"entryPoint":".github/workflows/provenance.yaml"},"parameters":{},"environment":{ "/* GitHub context */"}},"metadata":{"buildInvocationID":"3230206088-1","completeness":{"parameters":true,"environment":false,"materials":false},"reproducible":false},"materials":[{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6"}}]}}
Index: 4920248
IntegratedTime: 2022-10-11T21:18:18Z
UUID: 24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
Body: {
  "IntotoObj": {
    "content": {
      "hash": {
        "algorithm": "sha256",
        "value": "2268194f93bf9db7de6344a665ae38de791e7adc30ecc315000b77b24d0a4a60"
      },
      "payloadHash": {
        "algorithm": "sha256",
        "value": "9db814f8b10fc3d9442eb322c265fb47105a85fc35fa62a660a83f5bb0f66622"
      }
    },
    "publicKey": "LS0tLS1CRUdJTiBDRVJUSUZJQ0FURS0tLS0tCk1JSUR2RENDQTBLZ0F3SUJBZ0lVQnQzRkpSUG9LQVpicU43M2VOaDk4QndRdWRZd0NnWUlLb1pJemowRUF3TXcKTnpFVk1CTUdBMVVFQ2hNTWMybG5jM1J2Y21VdVpHVjJNUjR3SEFZRFZRUURFeFZ6YVdkemRHOXlaUzFwYm5SbApjbTFsWkdsaGRHVXdIaGNOTWpJeE1ERXhNakV4T0RFNFdoY05Nakl4TURFeE1qRXlPREU0V2pBQU1Ga3dFd1lICktvWkl6ajBDQVFZSUtvWkl6ajBEQVFjRFFnQUV5NnNNY3FRcVhXcXJhclJONi95SmRlRnQ2L1VWUVI0QWh2ay8KRzBMT1BqRVd6ZHNSZFdvcUJiYWtUM05PWEdGOThjSWN3M29BS1ZSbUhKZkwvTGJPMDZPQ0FtRXdnZ0pkTUE0RwpBMVVkRHdFQi93UUVBd0lIZ0RBVEJnTlZIU1VFRERBS0JnZ3JCZ0VGQlFjREF6QWRCZ05WSFE0RUZnUVVtQlZ1CkhyTmtHVjVheUxHR2ErWkJ2V1Vvb29Zd0h3WURWUjBqQkJnd0ZvQVUzOVBwejFZa0VaYjVxTmpwS0ZXaXhpNFkKWkQ4d2dZUUdBMVVkRVFFQi93UjZNSGlHZG1oMGRIQnpPaTh2WjJsMGFIVmlMbU52YlM5emJITmhMV1p5WVcxbApkMjl5YXk5emJITmhMV2RwZEdoMVlpMW5aVzVsY21GMGIzSXZMbWRwZEdoMVlpOTNiM0pyWm14dmQzTXZaMlZ1ClpYSmhkRzl5WDJkbGJtVnlhV05mYzJ4ellUTXVlVzFzUUhKbFpuTXZkR0ZuY3k5Mk1TNHlMakF3T1FZS0t3WUIKQkFHRHZ6QUJBUVFyYUhSMGNITTZMeTkwYjJ0bGJpNWhZM1JwYjI1ekxtZHBkR2gxWW5WelpYSmpiMjUwWlc1MApMbU52YlRBU0Jnb3JCZ0VFQVlPL01BRUNCQVJ3ZFhOb01EWUdDaXNHQVFRQmc3OHdBUU1FS0RGaU1USTRabUl5Ck5UVTJaVFJpWkdOak5HWTVNalUxTWpZMU5HSm1ZbU5oT1dReVptSTRZell3SGdZS0t3WUJCQUdEdnpBQkJBUVEKUW5WcGJHUWdVSEp2ZG1WdVlXNWpaVEFkQmdvckJnRUVBWU8vTUFFRkJBOXdjbTlxWldOMExXOWhheTl2WVdzdwpIUVlLS3dZQkJBR0R2ekFCQmdRUGNtVm1jeTlvWldGa2N5OXRZV2x1TUlHSkJnb3JCZ0VFQWRaNUFnUUNCSHNFCmVRQjNBSFVBQ0dDUzhDaFMvMmhGMGRGcko0U2NSV2NZckJZOXd6alNiZWE4SWdZMmIzSUFBQUdEeU9taUpnQUEKQkFNQVJqQkVBaUI3T3VDOGtMSkFiMk9qK2ozL2ZQRFlqeFE1V1Z0cFNRM0VHU2hjQzJWQUFBSWdHVWd6VVdydQpPV2dRYmhaa2VrZm9GMzFHenQvRXh5NEhVVXJWZkJyMUdmc3dDZ1lJS29aSXpqMEVBd01EYUFBd1pRSXhBUDlpCk5yNHFFYU1pdlMySGErN2JIaTh1MncvbTZWczd1S21sN1FhRlFFaUN4K0l5TlZMNkh3c1BZTkxnNVEwT3JRSXcKZGMyRlozT0FPUXZxaXJ4MlhGbDBPMytpczFWYjB5Wi9ic09ud2IweTV2Y0h6SVoyT1B0ejV6eDcyZFY4L295SQotLS0tLUVORCBDRVJUSUZJQ0FURS0tLS0tCg=="
  }
}
```

In this case, the provenance is in the `Attestation` field. The response in this
case does not contain the verification, because `rekor-cli` already verifies the
LogEntry and its inclusion in Rekor. Howevre, it contains other details,
including the `Body.IntotoObj` object. The `payloadHash` in this object is the
SHA256 hash of the provenance.

TODO(#3333): Describe the relation between the cert in DSSE format, and the
public key in the response from `rekor-cli`.
