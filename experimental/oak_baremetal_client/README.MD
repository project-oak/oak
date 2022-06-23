# Oak Baremetal Client

A trivial gRPC client for communicating with the trusted runtime via the gRPC
endpoint exposed by the untrusted companion app.

## Starting the client

Running the client may be started via

```shell
cargo run --package=oak_baremetal_client
```

The client will read lines from stdin and sends a gRPC request to the loader for
each line. Responses are printed to stdout.
