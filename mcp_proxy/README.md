# mcp_proxy

> [!CAUTION] Experimental code, not ready for production use.

This is an HTTP proxy that intercepts responses from a target server and
verifies if they have been cryptographically endorsed using `cosign` and stored
in an OCI-compliant endorsement repository.

## Features

- Intercepts HTTP responses and calculates their SHA256 digest (acting as the
  "subject").
- Fetches the custom `index.json` from a configurable `endorsement_index_url`.
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
target_mcp_server_url = "http://localhost:8080/target_server"

[[filter]]
method = "your_rpc_method" # The MCP method to filter and verify
cosign_identity = "your_email@example.com" # Expected email identity of the endorser
cosign_oidc_issuer = "https://accounts.google.com" # OIDC issuer (e.g., for GitHub actions or Google accounts)
endorsement_index_url = "https://raw.githubusercontent.com/your_org/your_repo/refs/heads/main/index.json" # URL to your custom endorsement index.json
```

## Usage

```bash
# Ensure cosign is installed and in your PATH
# go install github.com/sigstore/cosign/cmd/cosign@latest

bazel run mcp_proxy -- --config=$PWD/mcp_proxy/config.toml
```

The proxy will start on `http://localhost:8080` (or as configured). All requests
to this proxy that match a filter's `method` will trigger endorsement
verification.

From Gemini CLI, run `/mcp refresh` and `/mcp desc`.

If the tool configuration of the MCP server was not endorsed according to the
policy set in the config, the client will print a message similar to the
following:

```text
✕ Error discovering tools from demo-proxy: Error POSTing to endpoint (HTTP 403): Endorsement verification failed for subject digest:
  sha256:3cfe8b08e6c9b30aaba15962630494e9ec143c7422ee7bee2de70874aa48dac2.
  Error: no endorsements found for subject HexDigest { psha2: "", sha1: "", sha2_256: "3cfe8b08e6c9b30aaba15962630494e9ec143c7422ee7bee2de70874aa48dac2", sha2_512: "", sha3_512: "", sha3_384: "",
  sha3_256: "", sha3_224: "", sha2_384: "" }

  The response from the server was not endorsed by the expected identity (Some("tiziano88@gmail.com")).

  To endorse this content, run the endorsement tool on the saved subject file:
  doremint blob endorse --file="/tmp/mcp_proxy/sha256:3cfe8b08e6c9b30aaba15962630494e9ec143c7422ee7bee2de70874aa48dac2" --repository=<path_to_repo> --valid-for=1d
  --claims="https://github.com/project-oak/oak/blob/main/docs/tr/claim/94503.md"
```

## Dependencies

- [Cosign](https://docs.sigstore.dev/cosign/overview/) (must be installed and
  available in your system's PATH).
