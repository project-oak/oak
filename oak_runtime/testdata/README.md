# Keys for unit testing

These sample keys are intended to be used for unit testing `oak_runtime`.

In order to create a new pair of public/private keys, run the following command:

```bash
./scripts/oak_sign generate --private-key=oak_runtime/testdata/test.key --public-key=oak_runtime/testdata/test.pub
```

To sign a Wasm module, run the following command:

```bash
./scripts/oak_sign sign --private-key=oak_runtime/testdata/test.key --input-file=oak_runtime/testdata/module.wasm --signature=oak_runtime/testdata/module.sign
```
