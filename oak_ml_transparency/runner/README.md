# Oak Model Evaluation Runner

This is a command line tool for running an evaluation on a model and generating
a claim about it.

See [`mnist`](../mnist) for an example model evaluation project.

## Build the runner

The runner is used inside a Docker image similar to the one in
[mnist Dockerfile](../mnist/Dockerfile), so we may need to build it for various
targets, including `musl`. Run the following under `oak_ml_transparency/runner`:

```console
$cargo build --release --target=x86_64-unknown-linux-musl
   Compiling runner v0.1.0 (/workspace/oak_ml_transparency/runner)
    Finished release [optimized] target(s) in 12.35s
```

To make it available in the Docker image, we upload this to ent. In the future,
we will provide a better provenance story for the runner.

```console
$./ent put ./runner/target/x86_64-unknown-linux-musl/release/runner
sha256:ed9c35c10c084dfe25b7c22a58d14ed090801fced7e292498da5c7e77853f6ea ↑ [ent-store]
```

## Run the runner

You can test the runner directly with `cargo run`:

```bash
cargo run -- \
--model=testdata/eval.py \
--model-name=mnist \
--eval-script=testdata/eval.py \
--output=claim.json
```

Note that this command uses `testdata/eval.py` as the model. This works because
currently the runner can accept any file as the model, and the test script does
not really use the model.
