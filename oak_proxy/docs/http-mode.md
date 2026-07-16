# L7 HTTP Mode & Attestation Observability (`--http`)

`oak_proxy` (`client` and `server`) can optionally operate at **Layer 7 (HTTP)**
to intercept request and response frames over the wire, providing standard
in-band attestation feedback and structured diagnostic error responses.

## Enabling HTTP Mode (Independent Configuration)

To launch `oak_proxy` with L7 HTTP inspection and header splicing enabled, pass
`--http` via CLI flag or set `mode = "http"` inside your TOML configuration
file:

```bash
# Client Proxy with L7 HTTP mode (injects X-Oak-Attestation into responses sent to Client App)
oak_proxy client --config=client.toml --http

# Server Proxy with L7 HTTP mode (injects X-Oak-Attestation into requests sent to Server App)
oak_proxy server --config=server.toml --http
```

**Note on Independent Deployment**: Both proxies do not need to enable `--http`
simultaneously. The `--http` flag independently configures whether that specific
proxy (`client` or `server`) inspects and injects `X-Oak-Attestation` headers
for the local application it directly connects to (`Client App` or
`Server App`). For example, you can run `oak_proxy server --http` alongside a
default TCP-mode `oak_proxy client` if only the backend service needs in-band
verification reports.

## 1. In-Band Attestation Header (`X-Oak-Attestation`)

When `--http` is enabled and a secure attestation session (Noise or TLS) is
established:

- **Server Proxy**: Intercepts decrypted HTTP request frames from the client
  proxy, splices `X-Oak-Attestation: <base64url>` into the headers before the
  `\r\n\r\n` boundary, and forwards the modified request to the local backend
  HTTP server.
- **Client Proxy**: Intercepts decrypted HTTP response frames from the server
  proxy, splices `X-Oak-Attestation: <base64url>` into the headers before the
  `\r\n\r\n` boundary, and forwards the modified response to the local HTTP
  client application.

For HTTP keep-alive connections with multiple requests/responses over the same
session stream, `oak_proxy` inspects each HTTP header frame and splices
`X-Oak-Attestation` into each HTTP request/response frame before forwarding it,
resuming L4 TCP pass-through for message bodies.

### Decoded Payload Schema (`OakAttestationFeedback`)

The base64url-encoded JSON payload inside `X-Oak-Attestation` contains verified
attestation claims extracted from `AttestationEvidence`:

```json
{
  "status": "verified",
  "handshake_handle": "8f3c2b1e9d0a4f5c6b7a8e9d0c1b2a3f...",
  "verification_time": "2026-07-16T12:00:00Z",
  "root_layer": {
    "platform": "AMD_SEV_SNP",
    "allow_debug": false
  },
  "workload_layer": {
    "workload_type": "OAK_CONTAINERS",
    "container_image_digest": "sha256:4a7e96a2c3b8f1..."
  },
  "session_keys": {
    "session_binding_public_key": "hex:04..."
  }
}
```

## 2. Structured HTTP 502 Error Responses

When `--http` is enabled and connection establishment or attestation
verification fails during `establish_noise_session` / TLS handshake, `oak_proxy`
emits an explicit `HTTP/1.1 502 Bad Gateway` response before closing the socket.

### Error Body Schema (`OakProxyFailureResponse`)

The JSON body (`Content-Type: application/json`) categorizes the failure code
(`attestation_verification_failed`, `upstream_connection_failed`,
`handshake_timeout`, `protocol_error`) and details what was received versus what
was expected:

```json
{
  "error_code": "attestation_verification_failed",
  "details": {
    "failure_reason": "Container digest not authorized by endorsement/v1",
    "expected_digests": ["sha256:4a7e96..."],
    "received_digest": "sha256:0000..."
  },
  "timestamp": "2026-07-16T12:00:00Z"
}
```

In default TCP mode (`mode = "tcp"`, when `--http` is omitted), `oak_proxy`
closes the socket upon failure without emitting HTTP text or JSON frames.
