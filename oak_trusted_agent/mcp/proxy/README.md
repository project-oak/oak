# MCP Endorsement Proxy

> [!CAUTION] Experimental code, not ready for production use.

HTTP proxy that intercepts MCP responses from a target server and verifies that
their SHA-256 digests carry a valid [Cosign] endorsement in a
content-addressable endorsement repository.

## How it works

1. Hashes each matching HTTP response body with SHA-256 to obtain the subject
   digest.
2. Queries `endorsement_repository_url` (`blobs/sha256/<hex_digest>` and
   digest-keyed indices mapping subjects to endorsement statements and
   statements to Cosign signature bundles).
3. Caches subject blobs and endorsement bundles in `/tmp/mcp_proxy`.
4. Verifies the bundle signature against the subject with
   [`cosign verify-blob`](https://docs.sigstore.dev/cosign/verifying/verify/#keyless-verification-using-openid-connect)
   for the configured `cosign_identity` and `cosign_oidc_issuer`.
5. Returns `HTTP 403 Forbidden` if no valid endorsement is found, printing the
   `doremint blob endorse` command needed to endorse the cached response.

## Configuration

Example `config.toml`:

```toml
target_mcp_server_url = "http://localhost:8080/target_server"

[[filter]]
method = "your_rpc_method"
cosign_identity = "your_email@example.com"
cosign_oidc_issuer = "https://accounts.google.com"
endorsement_repository_url = "https://raw.githubusercontent.com/your_org/your_repo/refs/heads/main"
```

## Usage

Requires `cosign` in `PATH`
(`go install github.com/sigstore/cosign/cmd/cosign@latest`):

```bash
export RUST_LOG=trex_client=debug,mcp_proxy=debug
bazel run //oak_trusted_agent/mcp/proxy:mcp_proxy -- --config="$PWD/oak_trusted_agent/mcp/proxy/config.toml"
```

The proxy listens on `http://localhost:8080` (or the configured address). From
Gemini CLI, run `/mcp refresh` and `/mcp desc`. If the MCP server's tool
configuration has not been endorsed by the expected identity, the client prints:

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

[Cosign]: https://github.com/sigstore/cosign
