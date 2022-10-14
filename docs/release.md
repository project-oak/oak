
# Oak transparent build and release

## Per-commit build and provenance generation

Every time a pull-request is merged to `main` the
`oak_functions_freestanding_bin` binary is built and uploaded to `ent`.
Similarly, a
[signed SLSA3+ provenance is generated](https://github.com/slsa-framework/slsa-github-generator/blob/04f1fe0c7b7902c9a95f4c7eef2dc04cf0f8e6a7/internal/builders/generic/README.md)
for it and uploaded to GitHub. The signed provenance is also uploaded to the
public instance of Rekor hosted by Sigstore at https://rekor.sigstore.dev, and
can be downloaded from it.


## Retrieving a previously-built binary and its provenance

To release a binary transparenty, you have to endorse it first, using the endorser tool (currently WIP). The endorser takes as input the hash of the binary and one or more provenances, then it verifies the provenace, and generates an endorsement statement. This section describes how the binary and its provenance can be obtained to use with the `endorsr tool`. For more details on using the endorser see [these instructions (currently WIP)](https://github.com/project-oak/transparent-release/tree/main/cmd).

Once a pull-request is merged to `main` and all CI steps are executed on branch
`main`, an automated comment is added to the pull-request containing the hash of
the `oak_functions_freestanding_bin` binary:

```bash
d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc  ./oak_functions_freestanding_bin/target/x86_64-unknown-none/release/oak_functions_freestanding_bin
```

### Step 1: Download the binary

The hash of the binary
(`d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc`) can be used
to download the binary from `ent`, with the following command using the
[ent HTTP API](https://github.com/google/ent#raw-http-api):

```bash
$ curl --output oak_functions_from_ent  https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha256:d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 2327k    0 2327k    0     0  3637k      0 --:--:-- --:--:-- --:--:-- 3636k
```

### Step 2: Download the provenance

The provenance can be downloaded from Rekor or the GitHub actions workflow that
generated the binary and its provenance (i.e.,
[Build Provenance](https://github.com/project-oak/oak/actions/workflows/provenance.yaml))

#### Download from Rekor

To fetch the provenance from Rekor, one has to first find the Rekor LogEntries
that refer to the binary (via its SHA256 hash), using the `search` command
provided by `rekor-cli`
([installation instructions](https://docs.sigstore.dev/rekor/installation/)):

```bash
$ rekor-cli search --sha d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc
Found matching entries (listed by UUID):
24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
```

Usually there is only one entry, but it is possible to get multiple entires.
Alternatively, one can use the SHA1 Git commit hash to find the provenances
corresponding to that commit hash:

```bash
$ rekor-cli search --sha 1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6
Found matching entries (listed by UUID):
24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
```

Note that `rekor-cli` by default uses https://rekor.sigstore.dev as the Rekor
server.

Using the UUID
(24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576),
one can retrieve the provenance:

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

In addition to the provenance (in `Attestation`), the response contains
additional fields, including the `Body.IntotoObj` object. The `payloadHash` in
this object is the SHA256 hash of the provenance.

Alternatively, the provenance can be retrieved, as part of a Rekor LogEntry,
using the Rekor HTTP API:

```bash
$ curl --output signed-provenance-entry https://rekor.sigstore.dev/api/v1/log/entries/24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 17907    0 17907    0     0  21765      0 --:--:-- --:--:-- --:--:-- 21758
```

The downloaded file is a JSON document. The provenance is included in the
`attestation.data` field as a base64-encoded string, and can be extracted using
the following command:

```bash
$ jq .[].attestation.data signed-provenance-entry | tr --delete '"' | base64 --decode
{"_type":"https://in-toto.io/Statement/v0.1","predicateType":"https://slsa.dev/provenance/v0.2","subject":[{"name":"oak_functions_freestanding_bin","digest":{"sha256":"d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc"}}],"predicate":{"builder":{"id":"https://github.com/slsa-framework/slsa-github-generator/.github/workflows/generator_generic_slsa3.yml@refs/tags/v1.2.0"},"buildType":"https://github.com/slsa-framework/slsa-github-generator@v1","invocation":{"configSource":{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6"},"entryPoint":".github/workflows/provenance.yaml"},"parameters":{},"environment":{ "/* GitHub context */"}},"metadata":{"buildInvocationID":"3230206088-1","completeness":{"parameters":true,"environment":false,"materials":false},"reproducible":false},"materials":[{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6"}}]}}
```

#### Downloading provenance from GitHub

The provenance and the signature over it can be downloaded directly from GitHub.
For `oak_functions_freestanding_bin` it is stored under the name
`oak_functions_freestanding_bin.intoto.jsonl`, as an attachment on the GitHub
actions workflow. This file is in
[DSSE format](https://github.com/secure-systems-lab/dsse/blob/master/protocol.md):

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

TODO(#3333): Describe the relation between the cert in DSSE format, and the public key
in the response from `rekor-cli`.
