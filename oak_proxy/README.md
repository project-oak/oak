# Oak Proxy: Transparent End-to-End Encryption

This project implements a dual-proxy system that uses the `oak_session` library
to create a transparent, end-to-end encrypted, and attested tunnel between a
client and a server machine. This allows standard, unmodified applications (like
a web browser or `curl`) to communicate with an unmodified backend server (like
a standard HTTP server) over a secure channel without requiring any changes to
the applications themselves.

## Motivation

The `oak_session` library provides a powerful implementation of end-to-end
encrypted and attested communication sessions. However, integrating it directly
requires both the client and server applications to be specifically adapted to
use the `oak_session` protocol for their transport layer.

This project addresses the challenge of leveraging `oak_session`'s security
guarantees in scenarios where modifying the client or server applications is not
feasible or desirable. By deploying a pair of proxies, we can intercept
plaintext traffic on both ends, tunnel it through a secure `oak_session`, and
deliver it to the destination, making the entire security layer transparent to
the applications.

## Architecture

The system consists of two main components: a client-side forward proxy and a
server-side reverse proxy. The `oak_session` is established exclusively between
these two proxies.

```text
  +----------------+      +---------------------+      +---------------------+      +-----------------+
  |                |      |                     |      |                     |      |                 |
  |   Client App   |----->|    Client Proxy     |=====>|    Server Proxy     |----->|   Server App    |
  |  (e.g. cURL)   | Plain|  (Forward Proxy)    | Oak Session over |  (Reverse Proxy)    | Plain| (e.g. HTTP Srv) |
  |                | TCP  |                     |    WebSocket     | TCP  |                 |
  +----------------+      +---------------------+      +---------------------+      +-----------------+
        ^                                          |                                      |
        |                                          |                                      |
        +------------------------------------------+--------------------------------------+
                         Plain TCP Response (Decrypted by Client Proxy)
```

### Components

- **Client Proxy (`//oak_proxy/client`)**: A forward proxy that runs on the
  client's machine. It listens for incoming plaintext TCP connections from local
  applications. For each connection, it establishes an `oak_session` with the
  Server Proxy, encrypts the traffic, and forwards it.
- **Server Proxy (`//oak_proxy/server`)**: A reverse proxy that runs on the
  server's machine. It listens for incoming encrypted connections from the
  Client Proxy. It decrypts the traffic and forwards the plaintext to the final
  backend application server.
- **Shared Library (`//oak_proxy/lib`)**: A shared Rust library containing the
  common logic for proxying, used by both the client and server binaries.

### How It Works

1. **Connection Start**: The client application is configured to connect to the
   Client Proxy's listening address (e.g., `localhost:9090`).
2. **Session Establishment**: When the Client Proxy receives a connection, it
   initiates an `oak_session` handshake with the Server Proxy. The current
   implementation uses an unattested session for simplicity. The handshake
   messages are exchanged over the WebSocket connection.
3. **Data Forwarding (Client to Server)**:
   - The Client Proxy reads raw plaintext bytes from the application's TCP
     stream.
   - It passes these bytes to its `ClientSession` instance, which encrypts them.
   - The `ClientSession` produces an encrypted Protobuf message.
   - The Client Proxy sends this message as a binary frame over the WebSocket to
     the Server Proxy.
   - The Server Proxy receives the binary WebSocket frame.
   - It passes the encrypted message to its `ServerSession`, which decrypts it.
   - The resulting plaintext is written to the TCP stream connected to the
     backend server.
4. **Data Forwarding (Server to Client)**: The process is reversed for the
   response.

### Transport Protocol

To ensure a standardized and robust transport layer, the communication between
the client and server proxies uses the **WebSocket** protocol.

- All communication, including the `oak_session` handshake and subsequent data
  transfer, occurs over a WebSocket connection.
- Protobuf messages are serialized and sent as binary frames
  (`MessageType::Binary`) within the WebSocket protocol.

This approach eliminates the need for a custom framing mechanism, as WebSockets
provide a message-based transport that naturally delineates each Protobuf
message. The WebSocket handling logic is located in the
`//oak_proxy/lib/src/websocket.rs` module.

## Security Model

- **Trust Boundary**: The `oak_session` secures the channel between the two
  proxies. The traffic between the local application and its corresponding proxy
  is plaintext. This is considered secure as long as the proxy and the
  application are running on the same trusted machine (e.g., on the `localhost`
  network).
- **Attestation**: When attestation is enabled, the Client Proxy and Server
  Proxy will cryptographically verify each other's identity and execution
  environment. The trust does not extend to the unmodified client and server
  applications themselves, but it guarantees that the tunnel is established
  between legitimate, attested proxy instances.

## Usage

### Prerequisites

Ensure you have Bazel installed and the project dependencies are set up
correctly by running `just bazel-repin-all` from the root of the `oak`
repository.

### 1. Create Configuration Files

The proxies are configured using TOML files. Create two files: `client.toml` and
`server.toml`. See the [Configuration](#configuration) section for details on
the available options.

**Example `server.toml` (Unattested):**

```toml
listen_address = "127.0.0.1:8081"
backend_address = "127.0.0.1:8080"
```

**Example `client.toml` (Unattested):**

```toml
listen_address = "127.0.0.1:9090"
server_proxy_url = "ws://127.0.0.1:8081"
```

### 2. Build the Proxies

Build both the client and server binaries using Bazel:

```bash
bazel build //oak_proxy/client //oak_proxy/server
```

### 3. Run the Server Proxy

The server proxy listens for encrypted traffic from the client proxy and
forwards decrypted traffic to your backend application.

Start a simple backend server to test with. For example, use `netcat` to listen
on port 8080 and print any received data to the console:

```bash
nc -l -p 8080
```

Now, run the server proxy in a separate terminal, pointing it to your
configuration file:

```bash
bazel run //oak_proxy/server -- --config server.toml --listen-address "127.0.0.1:8081"
```

You should see the output: `[Server] Listening on 127.0.0.1:8081`.

### 4. Run the Client Proxy

The client proxy listens for plaintext traffic from your application and
forwards it over the secure tunnel to the server proxy.

Run the client proxy in a third terminal:

```bash
bazel run //oak_proxy/client -- --config client.toml --listen-address "127.0.0.1:9090" --server-proxy-url "ws://127.0.0.1:8081"
```

You should see the output: `[Client] Listening on 127.0.0.1:9090`.

### 5. Send Traffic

Now, use any TCP-based application to send traffic to the client proxy's listen
port (`127.0.0.1:9090`). The traffic will be transparently encrypted, sent to
the server proxy, decrypted, and forwarded to the `netcat` backend.

Using `curl`:

```bash
curl -x http://127.0.0.1:9090 http://example.com
```

You will see the raw HTTP request printed in the terminal where `netcat` is
running. This demonstrates that the data has been successfully proxied and
decrypted.

## Configuration

The behavior of the client and server proxies is controlled by a TOML
configuration file passed via the `--config` command-line argument.

### Common Options

- `listen_address`: The `SocketAddr` (e.g., `"127.0.0.1:9090"`) where the proxy
  should listen for incoming connections.
- `attestation_generators`: (Optional) A list of generators to use for
  generating attestation evidence to send to the peer.
- `attestation_verifiers`: (Optional) A list of verifiers to use for validating
  the peer's attestation evidence.

### Client-Specific Options

- `server_proxy_url`: The WebSocket `Url` of the server proxy.

### Client CLI Flags

- `--http-error-on-fail`: (Optional, Boolean) If set, the client proxy returns an **HTTP 502 Bad Gateway** response to the connected application if the handshake or attestation with the server proxy fails.
  - **Default**: `false` (Connection is dropped/reset silently on failure).
  - **Use Case**: Useful when the client application is an HTTP user agent (like a browser or `curl`) that can render a helpful error message instead of a generic connection error.

### Server-Specific Options

- `backend_address`: The `SocketAddr` of the final backend application where
  plaintext traffic should be forwarded.
- `backend_command`: (Optional) A command to execute a backend process that the
  server proxy will manage. The backend command should be configured with flags
  to listen in `backend_address`. It has the following structure:
  - `cmd`: The command to execute.
  - `args`: A list of arguments for the command.
  - `restart_policy`: Defines the behavior when the process exits. Can be
    `terminate` (default, exits the proxy), `always` (restarts the process), or
    `never` (does nothing).

### Attestation Modes

The presence of the `attestation_generators` and `attestation_verifiers`
sections determines the attestation mode:

1. **Unattested (Default)**: If both are omitted, the session is unattested.
2. **Unidirectional Attestation**: If one proxy has a `generator` and the other
   has a `verifier`, the session is unidirectionally attested.
3. **Bidirectional Attestation**: If both proxies have `generator` and
   `verifier` sections, the session is mutually attested.

### Example: Bidirectional Confidential Space Attestation

This example shows how to configure both proxies to generate and verify
Confidential Space attestations.

**`server.toml`**


```toml
listen_address = "127.0.0.1:8081"
backend_address = "127.0.0.1:8080"

# Generate our own Confidential Space attestation.
[[attestation_generators]]
type = "confidential_space"

# Verify the client's Confidential Space attestation.
[[attestation_verifiers]]
type = "confidential_space"
# Download from https://confidentialcomputing.googleapis.com/.well-known/confidential_space_root.crt
root_certificate_pem_path = "/path/to/confidential_space_root.crt"
# Optional: Restrict allowed container images
# expected_image_digests = ["sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"]
# Optional: Use a signed policy for allowed images
# signed_policy_path = "/path/to/policy.json"
# policy_signature_path = "/path/to/policy.sig"
# policy_public_key_pem_path = "/path/to/key.pem"
```

### Signed Policy Format

If using `signed_policy_path`, the policy file must be a valid **in-toto Statement** (v1).

Example `policy.json`:

```json
{
  "_type": "https://in-toto.io/Statement/v1",
  "subject": [
    {
      "name": "gcr.io/my-project/my-image",
      "digest": {
        "sha256": "cc564c5f64a18fc6e53dd737ec19774b68b609eb59cac4f13dcfd25cb61f3f68"
      }
    },
    {
      "name": "gcr.io/my-project/other-image",
      "digest": {
        "sha256": "33e3d4a3a7b79ec43c89803c1dbb1e15317b72f78e9e2ed86d8ff9c1d1431380"
      }
    }
  ],
  "predicateType": "https://example.com/custom/v1",
  "predicate": {}
}
```

**Schema Details:**

- **`_type`**: Required. Must be `https://in-toto.io/Statement/v1`.
- **`subject`**: Required. A list of artifacts covered by this policy.
  - **`name`**: (Optional) Human-readable name or URI of the artifact (e.g., image URL).
  - **`digest`**: Required. A map of cryptographic digests.
    - **`sha256`**: Required. The SHA-256 digest of the container image (hex-encoded).
- **`predicateType`**: Required. URI identifying the policy type (e.g., `https://example.com/custom/v1`).
- **`predicate`**: (Optional) Additional policy data (ignored by `oak_proxy` for digest verification).

This format follows the [in-toto Statement Specification](https://github.com/in-toto/attestation/blob/main/spec/v1/statement.md).


**`client.toml`**

```toml
listen_address = "127.0.0.1:9090"
server_proxy_url = "ws://127.0.0.1:8081"

# Generate our own Confidential Space attestation.
[[attestation_generators]]
type = "confidential_space"

# Verify the server's Confidential Space attestation.
[[attestation_verifiers]]
type = "confidential_space"
# Download from https://confidentialcomputing.googleapis.com/.well-known/confidential_space_root.crt
root_certificate_pem_path = "/path/to/confidential_space_root.crt"
```

## Extending Attestation

The proxy is designed to be extensible with new attestation flows. This is
achieved by adding new variants to the `GeneratorConfig` and `VerifierConfig`
enums in `//oak_proxy/lib/src/config/mod.rs`.

### How to Add a New Attestation Type

Let's say you want to add a new attestation mechanism called
"MyCustomAttestation".

1. **Create a New Module**:
   - Create a new file for your attestation logic, for example
     `//oak_proxy/lib/src/config/my_custom_attestation.rs`.
   - In this new file, define `MyCustomAttestationGeneratorParams` and
     `MyCustomAttestationVerifierParams` structs to hold any parameters needed
     for your attestation (e.g., file paths, endpoint URLs). Make sure they
     derive `serde::Deserialize`.

2. **Integrate with the Config Module**:
   - In `//oak_proxy/lib/src/config/mod.rs`, declare your new module with
     `pub mod my_custom_attestation;`.
   - Import your new param structs.
   - Add new variants to the `GeneratorConfig` and `VerifierConfig` enums,
     referencing your new structs:

     ```rust
     // in //oak_proxy/lib/src/config/mod.rs

     // Import your params
     use self::my_custom_attestation::{MyCustomAttestationGeneratorParams, MyCustomAttestationVerifierParams};

     #[derive(Deserialize)]
     #[serde(tag = "type", rename_all = "snake_case")]
     pub enum GeneratorConfig {
         ConfidentialSpace(ConfidentialSpaceGeneratorParams),
         MyCustomAttestation(MyCustomAttestationGeneratorParams), // Your new variant
     }

     #[derive(Deserialize)]
     #[serde(tag = "type", rename_all = "snake_case")]
     pub enum VerifierConfig {
         ConfidentialSpace(ConfidentialSpaceVerifierParams),
         MyCustomAttestation(MyCustomAttestationVerifierParams), // Your new variant
     }
     ```

3. **Implement the `apply` Method**:
   - In your new module (`my_custom_attestation.rs`), implement the `apply`
     method for your param structs. This method takes a `SessionConfigBuilder`
     and should add the appropriate `Attester`, `Endorser`, `Binder`, or
     `Verifier` to it.

   - For the generator:

     ```rust
     // in //oak_proxy/lib/src/config/my_custom_attestation.rs
     impl MyCustomAttestationGeneratorParams {
         pub fn apply(&self, builder: SessionConfigBuilder) -> anyhow::Result<SessionConfigBuilder> {
             // 1. Create instances of your custom attester, endorser, and binder.
             // 2. Add them to the builder.
             // Ok(builder.add_self_attester(...).add_self_endorser(...).add_session_binder(...))
         }
     }
     ```

   - For the verifier:

     ```rust
     // in //oak_proxy/lib/src/config/my_custom_attestation.rs
     impl MyCustomAttestationVerifierParams {
         pub fn apply(&self, builder: SessionConfigBuilder) -> anyhow::Result<SessionConfigBuilder> {
             // 1. Create an instance of your custom verifier.
             // 2. Add it to the builder.
             // Ok(builder.add_peer_verifier_with_key_extractor(...))
         }
     }
     ```

4. **Update the `match` Statements**:
   - In `//oak_proxy/lib/src/config/mod.rs`, add a branch to the `match`
     statement in the `apply` methods for `GeneratorConfig` and `VerifierConfig`
     to call your new implementation.

5. **Use in Configuration**:
   - You can now use your new type in the TOML configuration files:

     ```toml
     [[attestation_generators]]
     type = "my_custom_attestation"
     # ... any other params for your struct
     ```

## Testing

The proxy includes an integration test that simulates the manual steps described
in the "Usage" section. It programmatically creates configurations, starts the
proxies, and verifies that data can be sent and received correctly.

To run the test:

```bash
bazel test //oak_proxy:oak_proxy_integration_test
```

## Future Work

This implementation is a functional proof-of-concept. Future enhancements could
include:

- [ ] **Configuration Caching**: Avoid re-creating the `SessionConfig` and its
      associated generators and verifiers for each new connection to improve
      performance.
- [ ] **Robustness**: Improve error handling and connection management for
      production use cases.
- [ ] **Packaging**: Create distributable packages for easier deployment of the
      proxies on client and server machines.
