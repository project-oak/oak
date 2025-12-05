# mcp_proxy

This is an HTTP proxy that intercepts responses from a target server and
verifies if they have been cryptographically endorsed using `cosign` and stored
in an OCI-compliant endorsement repository.

## Features

- Intercepts HTTP responses and calculates their SHA256 digest (acting as the
  "subject").
- Fetches the OCI `index.json` from a configurable `http_index_prefix`.
- Locates associated endorsement entries in the `index.json` based on the
  subject digest and `tr.type: "endorsement"` annotation.
- Caches both subject data and endorsement bundles locally in `/tmp/mcp_proxy`
  to avoid redundant network requests.
- Performs cryptographic signature verification of the endorsement bundle
  against the subject using
  [`cosign verify-blob`](https://docs.sigstore.dev/cosign/verifying/verify/#keyless-verification-using-openid-connect).
- Enforces identity verification by checking the `cosign_identity` and
  `cosign_oidc_issuer` specified in the configuration.
- If no valid endorsement is found, or if verification fails, the proxy returns
  an `HTTP 403 Forbidden` error to the client, along with instructions on how to
  endorse the content.

## Configuration

The proxy requires a `config.toml` file for its settings.

**Example `config.toml`:**

```toml
target_base_url = "http://localhost:8080/target_server"

[[filter]]
method = "your_rpc_method" # The MCP method to filter and verify
cosign_identity = "your_email@example.com" # Expected email identity of the endorser
cosign_oidc_issuer = "https://accounts.google.com" # OIDC issuer (e.g., for GitHub actions or Google accounts)
http_index_prefix = "https://raw.githubusercontent.com/your_org/your_repo/refs/heads/main/" # URL to the root of your OCI endorsement repository
```

## Usage

```bash
# Ensure cosign is installed and in your PATH
# go install github.com/sigstore/cosign/cmd/cosign@latest

just build-mcp-proxy
./bin/mcp_proxy -config=./mcp_proxy/config.toml
```

The proxy will start on `http://localhost:8080` (or as configured). All requests
to this proxy that match a filter's `method` will trigger endorsement
verification.

From Gemini CLI, run `/mcp refresh` and `/mcp desc`.

## Dependencies

- [Cosign](https://docs.sigstore.dev/cosign/overview/) (must be installed and
  available in your system's PATH).
