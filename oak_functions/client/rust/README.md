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

The client has basic verification logic for verifying the configuration sent
from the server.

If the data sent from the server to the client also contains a log entry from
Rekor, the client verifies that too.

### Steps for testing the verification of a log entry from Rekor

- Created
  [a sample endorsement file](oak_functions/client/rust/testdata/endorsement.json)
  for
  [a sample provenance file](https://github.com/project-oak/transparent-release/blob/main/testdata/provenances/15dc16c42a4ac9ed77f337a4a3065a63e444c29c18c8cf69d6a6b4ae678dca5c.json).
- Signed and uploaded it to Rekor (https://rekor.sigstore.dev), as described
  [here](https://github.com/sigstore/rekor/blob/main/types.md#pkixx509). The
  resulting entry in Rekor has UUID
  `bb05be1bd813f8afb7b77b2d9f7be5ae25b396d111c7a26a04b785c48c277372`.
- The
  [log entry](https://rekor.sigstore.dev/api/v1/log/entries/bb05be1bd813f8afb7b77b2d9f7be5ae25b396d111c7a26a04b785c48c277372)
  is what the server sends to the client, along with the endorsement file for
  verification.
