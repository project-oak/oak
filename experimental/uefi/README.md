# Experimental UEFI app and untrusted loader

This directory contains the following:

- `runtime`: common business logic that should run in a VM
- `app`: UEFI application that wraps `runtime` for execution under UEFI
- `loader`: wrapper around `qemu` that loads the above and exposes a gRPC server
  for communicating with the runtime
- `client`: a trivial gRPC client for communicating with the loader/runtime.

## Loader

To run the loader, build the loader and `app`, and run:

```shell
RUST_LOG=debug target/debug/uefi-loader experimental/uefi/app/target/x86_64-unknown-uefi/debug/uefi-simple.efi
```

This will start listening for connections on `127.0.0.1:8000` by default.

## Client

Running the client requires no specific arguments:

```shell
target/debug/uefi-client
```

The client will read lines from stdin and sends a gRPC request to the loader for
each line. Responses are printed to stdout.

## Communication between VM code and the outside world

We assume there's two serial ports on the system:

- the first one will be used for console stdio and any logs produced by the app
- the second serial port is used by the app.
