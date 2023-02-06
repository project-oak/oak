# Lookup Data Checker

The binary in this directory checks the correctness of the lookup data file.

Usage (e.g., after running `./scripts/docker_sh`):

```bash
RUST_LOG=debug cargo run --manifest-path=oak_functions/lookup_data_checker/Cargo.toml -- --file-path=oak_functions/examples/weather_lookup/testdata/lookup_data_weather_sparse_s2
```

to get

```bash
...
[36.9581960, 149.3685880], [36.9108250, 148.8116340], [143.1569150, -30.9774870]]} # Cell ID
[2023-01-12T13:02:18Z DEBUG lookup_data_checker] - {[66.2241310, -162.2377160]: [123, 34, 116, 101, 109, 112, 101, 114, 97, 116, 117, 114, 101, 95, 100, 101, 103, 114, 101, 101, 115, 95, 99, 101, 108, 115, 105, 117, 115, 34, 58, 49, 55, 125]} # Location
[2023-01-12T13:02:18Z INFO  lookup_data_checker] Format is correct
```
