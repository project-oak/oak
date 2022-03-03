# Lookup Data Checker

The binary in this directory checks the correctness of the lookup data file.

Usage:

```bash
./scripts/docker_run RUST_LOG=debug cargo run --manifest-path=oak_functions/lookup_data_checker/Cargo.toml -- --file-path=weather_data_file
```
