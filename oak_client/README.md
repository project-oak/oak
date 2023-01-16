# Oak Functions Client

`oak_functions_client` is a command-line utility to invoke any instance of an
Oak Functions server over gRPC.

It reads the request payload from the `--request` flag, and prints the response
payload to standard output.

To compile:

```sh
cargo build --package=oak_functions_client
```

Example invocation:

```sh
./target/debug/oak_functions_client \
  --uri=http://localhost:8080 \
  --request=request_body
```

## Verification logic

The client may have a privacy policy that the server must conform to. If the
client has such a policy, before sending requests to the server, the client has
to verify the policy. To do this the client first requests the relevant
information (e.g., server configuration information, and endorsement evidence)
from the server. The exact details of the exchange of this information between
the server and the client is still unclear. However, the endorsement evidence is
an important part of it and must contain an endorsement statement about the
server binary, signed by the product team, and a LogEntry from Rekor (a
transparency log) to prove the inclusion of the endorsement statement in the
log.

Verifying the endorsement evidence, if required by the client policy, includes
verifying the Rekor LogEntry and the content of the endorsement file. In
particular, the SHA256 hash of the binary in the subject of the endorsement file
must be the same as the hash of the server binary (also provided to the client
in an attestation report). Checking the LogEntry involves verifying the
`signedEntryTimestamp` using Rekor's public key, and the signature in the body
of the LogEntry using Oak's public key (or more generally the product team's
public key).
