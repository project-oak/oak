# Oak functions `weather_lookup` example

This is an Oak Functions application that expects to receive geographic
coordinates (latitude and longitude) in the request, and responds with the
weather at that location, by looking it up in a lookup data set that is
periodically refreshed from an external source.

## Running manually

To build and run this example manually follow these steps:

1. Build the weather lookup Wasm module:

   ```shell
   cargo -Zunstable-options build --release \
       --target=wasm32-unknown-unknown \
       --manifest-path=./oak_functions/examples/weather_lookup/module/Cargo.toml \
       --out-dir=./oak_functions/examples/weather_lookup/bin
   ```

1. Build `oak_functions_loader` (with debugging enabled if needed):

   ```shell
   cargo build --manifest-path=./oak_functions/loader/Cargo.toml \
       --release \
       --features=oak-unsafe
   ```

1. Run `oak_functions_loader` with the Wasm module:

   ```shell
   ./oak_functions/loader/target/release/oak_functions_loader \
       --wasm-path=./oak_functions/examples/weather_lookup/bin/weather_lookup.wasm \
       --config-path=./oak_functions/examples/weather_lookup/config.toml
   ```

1. Invoke with:

   ```shell
   curl \
     --include \
     --fail-early \
     --http2 \
     --http2-prior-knowledge \
     --request POST \
     --data '{"lat":51,"lon":0}' \
     http://localhost:8080/invoke
   ```
