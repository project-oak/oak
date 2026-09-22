# Attested provenance

Publishes results computed inside [Confidential Space] so that a third party can
check what produced them without trusting whoever reports them.

Two binaries and a shared library:

|             |                                                                  |
| ----------- | ---------------------------------------------------------------- |
| `signer/`   | runs in the TEE, beside the workload, and signs what it produced |
| `verifier/` | runs anywhere, including a laptop with no TEE                    |
| `common/`   | the in-toto `statement` and the `envelope` around it             |

`common/statement.rs` both builds statements and checks the artifacts they name,
because the two sides have to agree on the digest algorithm and its spelling.

## What gets signed

The signer hashes the artifacts named on the command line, wraps their digests
in an [in-toto Statement], and asks the Confidential Space launcher for a token
whose `eat_nonce` is the digest of that statement. The launcher stamps the image
digest into the token, so the resulting claim reads: _the image that asked for
this token vouches for artifacts with these digests, and here is the predicate
describing them_.

The predicate is opaque to both binaries. Whoever adds a benchmark picks a
`predicateType` URI and emits whatever JSON object matches it, rather than
changing any Rust.

## Signing

```shell
signer \
  --subject        /out/report.jsonl \
  --subject-digest gpt-oss:20b=sha256:2f1e… \
  --predicate-type https://project-oak.dev/attestation/model-eval/v1 \
  --predicate      /out/predicate.json \
  --out            /out/signed_statement.json
```

Outside a TEE, pass `--no-attestation` to emit the statement with an empty
`assertions` map. The verifier rejects it.

## Verifying

```shell
verifier \
  --statement              /out/signed_statement.json \
  --subject                /out/report.jsonl \
  --unchecked-subject      gpt-oss:20b \
  --expected-image-prefix  europe-docker.pkg.dev/oak/trusted-eval/ \
  --expected-image-digest  sha256:dead… \
  --expected-predicate-type https://project-oak.dev/attestation/model-eval/v1
```

```text
Checks
  ✅ the envelope declares the in-toto media type
  ✅ the payload is an in-toto v1 Statement
  ✅ the predicate type is the expected one
  ✅ report.jsonl matches the digest in the statement
  ✅ every subject was re-hashed or waived
  ✅ a Confidential Space token binds this exact statement
  ✅ the workload image is the expected one
VERIFIED
  produced by  europe-docker.pkg.dev/oak/trusted-eval/garak:v1
  image        sha256:dead…
  attested at  2026-09-11T16:00:00Z
```

Checks accumulate rather than short-circuit, so one failure does not hide the
others. Exit status is non-zero unless every check passes.

`--expected-image-prefix` matches the start of the image reference, so it pins
the _repository path_ rather than an image: anyone who can push there passes it.
`--expected-image-digest` pins the image itself, by comparing the
`submods.container.image_digest` claim. Use both for anything that matters.

A subject that is neither re-hashed with `--subject` nor waived with
`--unchecked-subject` fails the run, so a statement cannot quietly pass while
half of what it covers went unexamined. Waiving is for subjects that cannot be
re-hashed locally, such as a model known only by digest.

The token is verified at its own `iat`. Confidential Space tokens expire after
about an hour, so verifying a stored statement at the current time would fail
the morning after it was produced. Do not work around this by writing a
timestamp into the envelope: it would be an unauthenticated copy of a claim the
token already makes.

## Envelope

```json
{
  "payloadType": "application/vnd.in-toto+json",
  "payload": "<base64 in-toto Statement>",
  "assertions": {
    "49128794-6056-4999-ab3b-00d22d8c2eee": "<base64 oak.attestation.v1.Assertion>"
  }
}
```

The payload is base64 rather than inline JSON because assertions bind the digest
of those exact bytes, which re-serialization would not preserve.

This is not a [DSSE] envelope. DSSE expects a detached signature over the
payload; Confidential Space instead returns a token whose nonce commits to the
payload digest, so the binding is checked differently and the field names would
mislead. Two costs follow. `payloadType` sits outside the signed bytes, so the
verifier asserts the expected constant rather than trusting what it reads. And
standard in-toto or cosign tooling cannot consume this envelope.

The assertion key is a random UUID, as Oak names attestation types in
`oak_proto_rust::attestation`. It denotes a Confidential Space token whose
`eat_nonce` commits to the payload digest, and it is defined as `ASSERTION_ID`
in `common/envelope.rs`. The verifier looks the assertion up by that ID rather
than iterating the map, because requiring every entry to pass would accept an
unsigned envelope vacuously.

## What the claim does and does not prove

The token proves that the named image asked for a nonce over this statement. It
does not by itself prove the image _computed_ the artifacts rather than hashing
bytes handed to it from outside.

The gap closes because Confidential Space does not let the VM operator change
what the container runs unless the image opts in. Any image using the signer
must therefore leave `tee.launch_policy.allow_cmd_override` unset, and must keep
`tee.launch_policy.allow_env_override` narrow enough that nothing in it can
redirect which files are hashed.

## Where the signer has to run

In the same image as the workload that produced the artifacts. The launcher
issues tokens naming whoever asks, so a standalone signing image would attest
only itself, saying nothing about the benchmark or the model. Any process in the
container can reach `/run/container_launcher/teeserver.sock`, so the signer adds
no privilege that a shell script in the same image lacks.

[Confidential Space]:
  https://cloud.google.com/confidential-computing/confidential-space/docs/confidential-space-overview
[DSSE]: https://github.com/secure-systems-lab/dsse
[in-toto Statement]:
  https://github.com/in-toto/attestation/blob/main/spec/v1/statement.md
