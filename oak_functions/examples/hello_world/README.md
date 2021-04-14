# Oak functions `hello world` example

This is a simple Oak functions example that expects to receive a name in the
request, and responds with `Hello $name!`.

## Running manually

To build and run this example manually follow these steps:

1. Build the Wasm module:

   ```shell
   cargo -Zunstable-options build --release \
       --target=wasm32-unknown-unknown \
       --manifest-path=oak_functions/examples/hello_world/module/Cargo.toml \
       --out-dir=oak_functions/examples/hello_world/bin
   ```

1. Build the `loader` with debugging enabled if needed:

   ```shell
   cargo build --manifest-path=./oak_functions/loader/Cargo.toml \
       --release \
       --features=oak-unsafe
   ```

1. Run the `loader` with the Wasm module:

   ```shell
   ./oak_functions/loader/target/release/oak_functions_loader \
       --wasm-path=oak_functions/examples/hello_world/bin/hello_world.wasm \
       --lookup-data-path=""
   ```

1. Invoke with:

   ```shell
   curl --include --fail-early --request POST --data 'request-body' localhost:8080/invoke
   ```
