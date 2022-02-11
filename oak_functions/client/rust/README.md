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

## Verification logic

As part of the Remote Attestation handshake the server sends to the client some
additional info along with the attestation quote. The client verifies this
additional information according to its policy, before sending any requests to
the server. If the additional information contains a LogEntry from Rekor and an
accompanying endorsement file, then the client verifies the LogEntry and the
content of the endorsement file. In particular, the SHA256 hash of the binary in
the subject of the endorsement file must be the same as the hash of the binary
received in the attestation quote. Checking the LogEntry involves verifying the
`signedEntryTimestamp` using Rekor's public key, and the signature in the body
of the LogEntry using Oak's public key.
