# Test Keys for oak_session/tls

**⚠️ WARNING: These are TEST-ONLY keys. Do NOT use in production.**

This directory contains test certificates and private keys used exclusively for
unit testing and example code. These keys are intentionally committed to the
repository and have no security value.

## Files

| File                 | Description                                               |
| -------------------- | --------------------------------------------------------- |
| `test_ca.key`        | Test CA private key                                       |
| `test_ca.pem`        | Test CA certificate (trust anchor)                        |
| `test_server.key`    | Test server private key                                   |
| `test_server.pem`    | Test server certificate (signed by test CA)               |
| `test_client.key`    | Test client private key                                   |
| `test_client.pem`    | Test client certificate (signed by test CA)               |
| `test_untrusted.key` | Self-signed untrusted private key                         |
| `test_untrusted.pem` | Self-signed untrusted certificate (NOT signed by test CA) |

## Certificate Chain

```text
test_ca.pem (Root CA)
├── test_server.pem (Server cert, signed by CA)
└── test_client.pem (Client cert, signed by CA)

test_untrusted.pem (Self-signed, NOT in chain - for rejection testing)
```

## Usage

These keys are used by:

- `//oak_session/tls:oak_session_tls_test` - Unit tests
- `//oak_session/tls/example/grpc:client_server_test` - gRPC example

## Regenerating Keys

To regenerate the test keys:

```bash
# Generate CA
openssl req -x509 -newkey rsa:2048 -keyout test_ca.key -out test_ca.pem \
    -days 365 -nodes -subj "/CN=Test CA"

# Generate server key and CSR
openssl req -newkey rsa:2048 -keyout test_server.key -out test_server.csr \
    -nodes -subj "/CN=localhost"

# Sign server cert with CA
openssl x509 -req -in test_server.csr -CA test_ca.pem -CAkey test_ca.key \
    -CAcreateserial -out test_server.pem -days 365

# Generate client key and CSR
openssl req -newkey rsa:2048 -keyout test_client.key -out test_client.csr \
    -nodes -subj "/CN=test-client"

# Sign client cert with CA
openssl x509 -req -in test_client.csr -CA test_ca.pem -CAkey test_ca.key \
    -CAcreateserial -out test_client.pem -days 365

# Generate untrusted self-signed cert (for rejection testing)
openssl req -x509 -newkey rsa:2048 -keyout test_untrusted.key \
    -out test_untrusted.pem -days 365 -nodes -subj "/CN=untrusted.example.com"
```
