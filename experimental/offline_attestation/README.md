# Offline Attestation

## Running the example

Start an instance of the server:

```bash
RUST_LOG=debug cargo run --manifest-path=experimental/offline_attestation/server/Cargo.toml
```

In another terminal, run the client:

```bash
RUST_LOG=debug cargo run --manifest-path=experimental/offline_attestation/client/Cargo.toml
```
