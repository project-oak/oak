# Private Set Intersection

## To update this example

This example requires a valid signature of the `handler` module. So, whenever
the code is modified, the wasm module and the signature must be regenerated:

1. Build the example, including the Wasm module
1. Sign the module with the test key that is checked in the repository (only for
   test / debug use):

   ```bash
   ./scripts/oak_sign sign \
     --private-key=examples/keys/ed25519/test.key \
     --input-file=examples/private_set_intersection/bin/private_set_intersection_handler.wasm \
     --signature-file=examples/private_set_intersection/private_set_intersection_handler.sign
   ```
