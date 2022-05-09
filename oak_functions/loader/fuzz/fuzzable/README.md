# Oak Functions `fuzzable` example

The sole purpose of this example is to be able to create a Wasm file that could
be used for fuzzing the `WasmHandler` used in the Oak Functions loader. This
example is therefore different from conventional examples in that it does not
have a client and it does not have an `example.toml` file. This example is used
by the `wasm_invoke` fuzz-target in
`./oak_functions/loader/fuzz/fuzz_targets/wasm_invoke.rs`.
