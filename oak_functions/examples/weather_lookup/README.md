# Oak Functions `weather_lookup` example

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
   ./oak_functions/loader/target/x86_64-unknown-linux-musl/release/oak_functions_loader \
       --wasm-path=./oak_functions/examples/weather_lookup/bin/weather_lookup.wasm \
       --config-path=./oak_functions/examples/weather_lookup/config.toml
   ```

1. Invoke with:

   ```shell
   cargo run --manifest-path=./oak_functions/client/rust/Cargo.toml -- \
       --uri=http://localhost:8080,
       --request={\"lat\":52,\"lon\":0}
   ```

Alternatively, the `runner` could be used to run this example:

```shell
./scripts/runner run-functions-examples --example-name=weather_lookup
```

## Cloud Run Deploy

Use the following script to deploy the service on Cloud Run.

```shell
./oak_functions/examples/weather_lookup/scripts/cloud_run_deploy run-functions-examples --example-name=weather_lookup
```

The script:

1. Deploys the weather-lookup service in Cloud Run.
2. Deploys a Cloud Endpoint service for connecting to the service on Cloud Run.
3. Sends a request to the Cloud Endpoints URL to test that the deployment has
   been successful.
