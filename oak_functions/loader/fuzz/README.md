# Oak Functions Fuzzing

## To update

Run:

```bash
./scripts/runner run-cargo-fuzz --build-deps -- -max_total_time=2
```

and

```bash

git add `/workspace/oak_functions/loader/fuzz/fuzz_targets/data/fuzzable.wasm`
git commit -m "Update fuzz target Wasm module"

```
