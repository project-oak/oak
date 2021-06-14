# Oak Functions Client

`oak_functions_client` is a command-line utility to invoke any instance of an
Oak Functions server over gRPC.

It reads the request payload from the `--request` flag, and prints the response
payload to standard output.

To compile:

```sh
cargo build \
  --manifest-path=./oak_functions/client/rust/Cargo.toml
```

Example invocation:

```sh
./oak_functions/client/target/debug/oak_functions_client \
  --uri=http://localhost:8080 \
  --request=request_body
```
