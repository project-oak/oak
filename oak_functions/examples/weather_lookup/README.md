# Oak Functions `weather_lookup` example

This is an Oak Functions application that expects to receive geographic
coordinates (latitude and longitude) in the request, and responds with the
weather at that location, by looking it up in a lookup data set that is
periodically refreshed from an external source.

## Lookup data format

The lookup data is composed of the individual locations for which weather data
is available, plus a special index entry.

For each weather location, the corresponding entry has an 8-byte key obtained by
concatenating the latitude and longitude, respectively, in millidegrees, each
serialized as an 4-byte big endian signed integer and then concatenated
together.

For instance, the key for the location corresponding to coordinates
`(14.12°, -19.88°)` is the byte sequence
`[0x00, 0x00, 0x37, 0x28, 0xFF, 0xFF, 0xF8, 0x3C]`:

`[0x00, 0x00, 0x37, 0x28] -> 0x00003728 -> 14120m° -> 14.120°`
`[0xFF, 0xFF, 0xB2, 0x58] -> 0xFFFFB258 -> -19880m° -> -19.880°`

Additionally, the index entry is stored under the special key with value `index`
(encoded as a UTF-8 string), and contains as value all the keys of the other
entries, concatenated next to each other.

The Wasm logic of the lookup module first loads the special `index` entry and
parses the keys by splitting the value in 8-bytes chunks, and each chunk further
in two 4-bytes chunks, then transforms them into latitude and longitude pairs,
and finds the nearest entry by computing the distance between each location and
the location from the client request, by linearly scanning the list of keys from
the index. Once the key of the nearest location is found, the module then
performs an additional lookup with that specific key and returns the
corresponding value to the client.

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
