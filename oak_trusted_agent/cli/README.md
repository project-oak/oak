# Oak Trusted Agent CLI

Command-line client for talking to an [Oak Trusted Agent] from a terminal over
an attested, end-to-end encrypted [Oak Proxy] channel.

```text
oak_trusted_agent_cli -> oak_proxy_client -> (Oak Session over WebSocket)
                      -> oak_proxy_server -> agent -> Wasm sandbox
```

The CLI speaks the `TrustedAgentService` streaming gRPC interface
([trusted_agent.proto]). `open --agent-url <URL>` opens a stream, which gets its
own agent sandbox for as long as the stream is open, and then works like a small
terminal of its own:

- Each line you type (followed by Enter) is sent to the agent as a new turn on
  the same stream, and the agent's reply is printed before the next prompt. Your
  messages are prompted with `user$` and the agent's replies are labeled
  `trusted-agent$`.
- Typing `close`, or ending the input with Ctrl-D, closes the stream, which ends
  the agent session.

Every `open` has its own stream and sandbox, so running it several times (e.g.
in different terminals) starts independent sessions that don't affect each
other.

The gRPC channel itself is plaintext: point `--agent-url` at the listen address
of a local Oak Proxy client, which verifies the agent's attestation before it
forwards any data. If verification fails, the proxy client closes the connection
and `open` fails.

## Demo

This walkthrough connects to an agent deployed with
[`oak_trusted_agent/agent/terraform`](../agent/README.md), shows why its
attestation passes (or fails) verification, and sends it requests over several
turns.

Build the tools from the Oak repository root:

```shell
nix develop --command bazel build \
  //oak_proxy/client \
  //oak_attestation_verification_cli \
  //oak_trusted_agent/cli:oak_trusted_agent_cli \
  //oak_trusted_agent/mcp:generate_reference_values
```

### 1. Start an Oak Proxy client that saves the agent's attestation

Copy [`proxy_client.toml`](proxy_client.toml) and fill in the placeholders:
`server_proxy_url` is the `server_proxy_url` Terraform output, and the digest in
`container_reference_prefix` is the digest of the agent image the client trusts.
The client saves the attestation it receives from the agent to
`attestation_output_file`, whether or not it passes verification.

```shell
cp oak_trusted_agent/cli/proxy_client.toml /tmp/agent_proxy_client.toml
# Edit the placeholders in /tmp/agent_proxy_client.toml, then:
RUST_LOG=info ./bazel-bin/oak_proxy/client/client --config=/tmp/agent_proxy_client.toml
```

### 2. Open a stream

In another terminal:

```shell
./bazel-bin/oak_trusted_agent/cli/oak_trusted_agent_cli open --agent-url=http://127.0.0.1:8080
```

```text
✅ Opened a stream to http://127.0.0.1:8080.
Type a message and press Enter to send it. Type `close` to end the session.
user$
```

Opening the stream makes the proxy client perform the attested handshake with
the agent and save the agent's attestation. If the proxy client can't reach the
agent at all, it saves nothing, so remove any attestation file left from an
earlier run before opening a stream (`rm -f /tmp/agent_attestation.binpb`).

### 3. Verify the saved attestation

While the stream is open, generate reference values that describe the agent you
expect in a third terminal, and check the saved attestation against them:

```shell
./bazel-bin/oak_trusted_agent/mcp/generate_reference_values \
  --root-certificate-pem-path=oak_attestation_gcp/data/confidential_space_root.pem \
  --container-reference-prefix=<the prefix from the proxy client config> \
  --output=/tmp/agent_reference_values.binpb

./bazel-bin/oak_attestation_verification_cli/oak_attestation_verification_cli \
  --attestation=/tmp/agent_attestation.binpb \
  --reference-values=/tmp/agent_reference_values.binpb
```

The report marks each check (timestamp, session handshake, attestation token,
container image, session binding, ...) with ✅ or ❌, and the timestamp shows
when the attestation was received.

### 4. Talk to the agent

Back in the CLI, type a message at the `user$` prompt and press Enter. Each
message is a new turn on the same stream and sandbox:

```text
user$ What is the value for key 42?
trusted-agent$ The value for key 42 is 84.
user$ What is the value for key 7?
trusted-agent$ The value for key 7 is 14.
```

### 5. Close the stream

```text
user$ close
✅ Closed the stream.
```

### When attestation fails

If the agent isn't running the expected image (for example, because
`container_reference_prefix` names a different digest), the proxy client refuses
to establish the session and closes the connection, so `open` fails before the
first prompt:

```text
❌ failed to open a stream to http://127.0.0.1:8080: failed to start the stream ...
If the agent is reached through an Oak Proxy client, the agent's attestation may have failed verification: ...
```

The proxy client still saved the attestation, so step 3 shows which check
failed, e.g. ❌ next to the container image. Because the session handshake was
aborted, the report also shows that the session handshake is missing.

## Testing

```shell
nix develop --command bazel test //oak_trusted_agent/cli:all
```

[Oak Proxy]: ../../oak_proxy/README.md
[Oak Trusted Agent]: ../agent/README.md
[trusted_agent.proto]: ../../proto/oak_trusted_agent/service/trusted_agent.proto
