# Running Average

## To update this example

1. Build the example, including the Wasm module
1. Push the module to GS via `./scripts/push_example -e running_average`
1. Fix the URL and hash in [`./oak_app_manifest.toml`](./oak_app_manifest.toml)
1. Sign the module with the test key that is checked in the repository (only for
   test / debug use):

   ```bash
   ./scripts/oak_sign sign \
     --private-key=examples/keys/ed25519/test.key \
     --input-file=examples/running_average/bin/running_average_handler.wasm \
     --signature-file=examples/running_average/running_average_handler.sign
   ```
