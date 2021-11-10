# Oak Functions `weather_lookup` example

This is an Oak Functions application that expects to receive geographic
coordinates (latitude and longitude) in the request, and responds with the
weather at that location, by looking it up in a lookup data set that is
periodically refreshed from an external source.

## Lookup data format

The lookup data is composed of the individual locations for which weather data
is available, plus a special set of index entries that can be used for finding
weather locations in the vicinity of the client's location. This example uses
40km as the cutoff for finding nearby weather data points, meaning that it would
only consider candidate weather data entries if they fall within a 40km radius
of the client's location. The value of this cutoff is an arbitrary choice, but
seems like a reasonable distance for which weather data might be relevant.

For each weather location, the corresponding entry has an 8-byte key obtained by
concatenating the latitude and longitude, each serialized as a 4-byte big endian
signed integer representing the respective value in microdegrees.

For instance, the key for the location corresponding to coordinates
`(14.12°, -19.88°)` is the byte sequence
`[0x00, 0xD7, 0x74, 0x40, 0xFE, 0xD0, 0xA7, 0xC0]`:

`[0x00, 0xD7, 0x74, 0x40] -> 0x00D77440 -> 14120000u° -> 14.120°`
`[0xFE, 0xD0, 0xA7, 0xC0] -> 0xFED0A7C0 -> -19880000u° -> -19.880°`

S2 Geometry (https://s2geometry.io/) cells are used to create the index lookup
entries. The surface of the earth is treated as a sphere and divided into a
number of cells (see https://s2geometry.io/devguide/s2cell_hierarchy). The
number of cells and their sizes are determined by the level. The level can range
from 0 to 30. At level 0 there are only 6 cells covering the entire earth. At
level 30 there are 7e18 cells (see
https://s2geometry.io/resources/s2cell_statistics). This example uses level 7
cells, as these have roughly similar sizes to the circular area around data
points with a 40km radius. If larger cells are used there would likely be fewer
index entries but with less tight coverage. Smaller cells would usually give
tighter coverage but a larger number of index entries.

Each cell is identified by a unique unsigned 64 bit integer. See
https://s2geometry.io/devguide/s2cell_hierarchy#s2cellid-numbering-again for
more details on how this is structured. These identifiers are converted to
tokens by generating a big endian hex string representation of the number and
trimming all trailing 0s. These tokens are used as the keys for the index
entries. At level 7 the cells have 5 byte tokens. The keys for the data items
are 8 bytes so key collisions between data entries and index entries are not
possible.

The value of each index entry consists of a concatenated list of the keys of the
weather data locations in the vicinity of the cell. All weather data locations
that could be within the cutoff (currently 40km) of any point within the cell
are included in the list. This is equivalent to finding all cells that partly
fall within the 40km radius. These are found by generating a cell covering
(using only level 7 cells) of a spherical cap centred at the data point with a
radius of 40km. See https://s2geometry.io/devguide/examples/coverings for more
information on coverings. Cell coverings for areas can be visualised using
https://s2.sidewalklabs.com/regioncoverer/.

## Lookup Logic

The Wasm logic of the lookup module first determines in which cell the current
location falls. It then looks up the index entry using the cell's ID token. If
it finds an index entry it iterates through all the potential weather data
locations. The keys of the weather locations encode their latitudes and
longitudes, so can be used to find the closest weather data location. If the
closest item lies within 40km of the client's location it uses the key to look
up the weather data associated with that item and returns it to the client.

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
       --request={\"lat\":0,\"lng\":0}
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
