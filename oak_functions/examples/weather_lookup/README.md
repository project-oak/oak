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
of the client's location. The choice of cutoff is based on a combination of the
likely range on which weather data can be relevant and the cell sizes used for
creating the index entries.

For each weather location, the corresponding entry has an 8-byte key obtained by
concatenating the latitude and longitude, respectively, in millidegrees, each
serialized as a 4-byte big endian signed integer and then concatenated together.

For instance, the key for the location corresponding to coordinates
`(14.12°, -19.88°)` is the byte sequence
`[0x00, 0x00, 0x37, 0x28, 0xFF, 0xFF, 0xF8, 0x3C]`:

`[0x00, 0x00, 0x37, 0x28] -> 0x00003728 -> 14120m° -> 14.120°`
`[0xFF, 0xFF, 0xB2, 0x58] -> 0xFFFFB258 -> -19880m° -> -19.880°`

To create the index lookup entries the surface of the earth is treated as a
sphere and divided into a number of cells with roughly similar sizes. The
earth's surface is divided into rows. Each row lies between two integer degrees
of latitude (e.g one row between 0° and 1°, and another between 1° and 2°). Each
row is divided into cells. We start with 360 cells per row at the equator. As we
move away from the equator each row becomes shorter, so the number of cells per
row is scaled by `cos(latitude_border)` to ensure that the width of the cells in
different rows are roughly similar. The lengths of the northern and southern
borders of a cell would be different. For simplicity, we use the longer border
of the two to calculate the number of cells. This means that most cells are
slightly wider than 100km at the widest point. All cells in a row have exactly
the same width, except for the last cell. The width of the last cell is slightly
adjusted to make sure that the widths of all the cells in a row sum up to
exactly 360° in spite of the rounding in floating point calculations.

The cells are identified by row- and column numbers. The row number of a cell is
the integer degree at its southern border (e.g. the row with the equator as its
southern border has row number 0). Rows in the southern hemishere have negative
row numbers. Cells within a row are numbered starting from 0 (the cell with 0°
longitude as its western border) and counting eastwards. Cells cannot have
negative column numbers. The key for an index entry is constructed by
concatenating the 2 byte signed big endian representation of the row and column
numbers for the cell. This means that index entries have 4 byte keys while
weather data entries have 8 byte keys, so key collisions are not possible.

The value of each index entry consists of a concatenated list of potential
weather data locations in the vicinity of the cell. All weather data locations
that could be within the cutoff (currently 40km) of any point within the cell
are included in the list. Each item in the list is exactly 16 bytes long. The
first 8 bytes is the key for looking up the weather data. The next 8 bytes
represent the approximate relative position of the weather data location
compared to the midpoint of the cell. The relative position is a projection of
the location onto a plane that forms a tangent to the sphere at the midpoint of
the cell. The origin of the plane is the midpoint of the cell where the plane
intersects the sphere and the y-axis points due North. The x and y coordinates
are both in meters and serialised as 4 byte big endian signed integers and
concatenated.

## Lookup Logic

The Wasm logic of the lookup module first determines in which cell the current
location falls and calculates the relative cartesian projection of the client's
location compared to the midpoint of the cell. It then looks up the index entry
using the key based on the cell identifier (row and column). If it finds an
index entry it iterates through all the potential weather data locations in the
list to find the closest weather data location using the relative cartesian
projections. The projections are accurate enough to find the closest weather
data, as the spherical surface is very close to being flat at these scales. If
the closest item lies within 40km of the client's location it uses the key to
lookup the weather data associated with that item and returns it to the client.

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
