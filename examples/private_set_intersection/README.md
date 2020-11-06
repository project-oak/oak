# Private Set Intersection

## To update this example

1. Build the example, including the Wasm module
2. Push the module to GS via
   `./scripts/push-example -e private_set_intersection`
3. Fix the URL and hash in [`./oak_app_manifest.toml`](./oak_app_manifest.toml)
4. Sign the module with the test key that is checked in the repository (only for
   test / debug use):

   ```bash
   ./scripts/oak_sign sign \
     --private-key=examples/keys/ed25519/test.key \
     --input-file=examples/private_set_intersection/bin/private_set_intersection.wasm \
     --signature-file=examples/private_set_intersection/private_set_intersection.sign
   ```
