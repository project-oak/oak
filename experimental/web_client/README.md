# Proof of Concept Oak Browser Client

Requires
[wasm-pack](https://rustwasm.github.io/wasm-pack/book/introduction.html) to
build.

## Testing

1. Start the relevant Oak instance via
   `./scripts/xtask --scope=all --logs run-oak-functions-examples --example-name=echo --client-variant=none`
2. Run the tests in this directory via `wasm-pack test --chrome --headless`
