# Keys for unit testing

These sample keys are intended to be used for unit testing `oak_runtime`.

In order to create a new pair of public/private keys, run the following command:

```bash
minisign -G -p test.pub -s test.key
```

To sign a Wasm module, run the following command:

```bash
minisign -Sm module.wasm -x module.sign -p test.pub -s test.key
```
