# Oak Functions Client

`oak_functions_client` is a command-line utility to invoke any instance of an
Oak Functions server over gRPC.

It reads the request payload from standard input, and prints the response
payload to standard output.

To compile:

```sh
cargo build \
  --manifest-path=./oak_functions/client/Cargo.toml
```

Example invocation:

```sh
echo request_body | ./oak_functions/client/target/debug/oak_functions_client \
  --uri=http://localhost:8080
```
