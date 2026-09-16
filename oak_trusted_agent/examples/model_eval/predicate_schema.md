# Model evaluation predicate

`https://project-oak.dev/attestation/model-eval/v1`

The predicate body carried by statements that report a model evaluation. The
signer does not interpret it, so this document, rather than any code, is what
producers and consumers agree on.

One statement covers one benchmark run. Benchmarks are signed separately so that
each can be re-run on its own, and so that a failure in one does not invalidate
the rest.

```json
{
  "benchmark": {
    "name": "hello_world",
    "version": "1"
  },
  "model": {
    "name": "gemma4:e2b",
    "digest": "sha256:aa4295ac10c3afb60e6d711289fc6896f5aef82258997b9efdaed6d0cc4cd8b8",
    "parameters": "2.0B",
    "quantization": "Q4_K_M",
    "sampling": { "temperature": 0.0, "seed": 0 }
  },
  "score": 1.0,
  "detail": { "trials": 10, "passed": 10 },
  "run": {
    "started_at": "2026-09-16T15:04:05Z",
    "finished_at": "2026-09-16T15:06:11Z"
  }
}
```

| Field       | Meaning                                                   |
| ----------- | --------------------------------------------------------- |
| `benchmark` | which test was run, and which revision of it              |
| `model`     | what answered; see below                                  |
| `score`     | the headline number, always in `[0, 1]`, higher is better |
| `detail`    | benchmark-specific, and the only part whose shape varies  |
| `run`       | RFC 3339 timestamps, unauthenticated; see below           |

Everything except `detail` has a fixed shape, so a reader can report the
benchmark, the model and the score without knowing what the benchmark is.

`score` is normalised to `[0, 1]` and oriented so that higher is better, even
where the benchmark reports otherwise. An attack success rate must therefore be
recorded as the resistance rate, with the raw figure kept in `detail`.

## Model identity

A score means nothing without knowing what produced it, which is why `model` is
part of the fixed shape rather than of `detail`.

`digest` is the Ollama manifest digest: a digest of the manifest listing the
weight files, not of the weights themselves. It identifies the model rather than
proving its contents. That is sufficient here because the weights are pulled at
image build time, so `submods.container.image_digest` in the attestation token
already covers the actual bytes. The same model also appears as a statement
subject, where it is descriptive only: a verifier cannot re-hash it and must
waive it with `--unchecked-subject`.

`sampling` records the settings that affect reproducibility. Without it, two
runs of the same benchmark against the same model can differ and neither
statement explains why.

## Timestamps

`run` is unauthenticated: it is written by the workload, and nothing stops a
workload from writing whatever it likes. It is there for humans reading the
report, not for verification.

The authenticated time is the attestation token's `iat`, which the verifier
prints as _attested at_. Prefer it whenever the difference matters.

## Changing this schema

Adding a field to `detail` needs no change here. Anything else is a new version
with a new URI, because `--expected-predicate-type` is how a verifier pins the
shape it is about to read.
