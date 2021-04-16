# Private Set Intersection

## To update this example

This example requires a valid signature of the `handler` module. So, whenever
the code is modified, the wasm module and the signature must be regenerated:

1. Build the example, including the Wasm module
1. Sign the module with the test key that is checked in the repository (only for
   test / debug use):

   ```bash
   ./scripts/oak_sign sign \
     --private-key=./examples/keys/ed25519/test.key \
     --input-file=./examples/bin/private_set_intersection_handler.wasm \
     --signature-file=./examples/private_set_intersection/private_set_intersection_handler.sign
   ```

## To publish the signature to rekor

rekor is a public verifiable log of signatures.

See <https://sigstore.dev/what_is_sigstore/> for details about rekor.

1. build the `rekor` CLI: <https://sigstore.dev/get_started/client/>
1. ```bash
   rekor upload \
     --artifact=<(base64 --decode <(sed -n '11,11p' ./examples/private_set_intersection/private_set_intersection_handler.sign | tr -d '[:space:]')) \
     --signature=<(base64 --decode <(sed -n '6,7p' ./examples/private_set_intersection/private_set_intersection_handler.sign | tr -d '[:space:]')) \
     --public-key=./examples/keys/ed25519/test.pub \
     --pki-format=x509
   ```

## To look up signatures from rekor

- by key:

  ```bash
  rekor search \
    --public-key=./examples/keys/ed25519/test.pub \
    --pki-format=x509
  ```

- by hash:

  ```bash
  rekor search \
     --artifact=<(base64 --decode <(sed -n '11,11p' ./examples/private_set_intersection/private_set_intersection_handler.sign | tr -d '[:space:]'))
  ```
