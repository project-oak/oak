# Oak Functions Load Test

`oak_functions_load_test` is a command-line utility to perform multiple requests
to an Oak Functions instance and collect statistics about the end-to-end latency
of the invocations.

```sh
cargo build \
  --manifest-path=./oak_functions/load_test/Cargo.toml
```

Example invocation:

```sh
./oak_functions/load_test/target/debug/oak_functions_load_test
```
