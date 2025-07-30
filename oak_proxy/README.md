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
  |  (e.g. cURL)   | Plain|  (Forward Proxy)    | Oak  |  (Reverse Proxy)    | Plain| (e.g. HTTP Srv) |
  |                | TCP  |                     |Session                     | TCP  |                 |
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
  common logic for data framing and proxying, used by both the client and server
  binaries.

### How It Works

1. **Connection Start**: The client application is configured to connect to the
   Client Proxy's listening address (e.g., `localhost:9090`).
2. **Session Establishment**: When the Client Proxy receives a connection, it
   initiates an `oak_session` handshake with the Server Proxy. The current
   implementation uses an unattested session for simplicity. The handshake
   messages are exchanged using the wire protocol described below.
3. **Data Forwarding (Client to Server)**:
   - The Client Proxy reads raw plaintext bytes from the application's TCP
     stream.
   - It passes these bytes to its `ClientSession` instance, which encrypts them.
   - The `ClientSession` produces an encrypted Protobuf message.
   - The Client Proxy sends this message to the Server Proxy using the wire
     protocol.
   - The Server Proxy receives and decodes the message from the wire.
   - It passes the encrypted message to its `ServerSession`, which decrypts it.
   - The resulting plaintext is written to the TCP stream connected to the
     backend server.
4. **Data Forwarding (Server to Client)**: The process is reversed for the
   response.

### Wire Protocol

Since TCP is a stream-based protocol, a framing mechanism is required to
delineate individual messages. This project uses a simple length-prefix framing
protocol:

- Each message (both for the handshake and for data transfer) is a Protobuf
  message serialized into bytes.
- Before sending the serialized message, its length is calculated as a 32-bit
  unsigned integer (`u32`).
- The 4-byte length is sent over the wire in big-endian order, immediately
  followed by the serialized message bytes.

```text
  +--------------------------------+-----------------------------------------+
  |         4-byte Length          |            Protobuf Message             |
  | (u32, Big-Endian)              |              (variable length)          |
  +--------------------------------+-----------------------------------------+
```

This ensures that the receiving end knows exactly how many bytes to read for the
next message. This logic is encapsulated in the `//oak_proxy/lib/framing`
module.

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

### 1. Build the Proxies

Build both the client and server binaries using Bazel:

```bash
bazel build //oak_proxy/client //oak_proxy/server
```

### 2. Run the Server Proxy

The server proxy listens for encrypted traffic from the client proxy and
forwards decrypted traffic to your backend application.

Start a simple backend server to test with. For example, use `netcat` to listen
on port 8080 and print any received data to the console:

```bash
nc -l -p 8080
```

Now, run the server proxy in a separate terminal. It will listen on port 8081
and forward to the `netcat` server on port 8080.

```bash
bazel run //oak_proxy/server -- --listen-address 127.0.0.1:8081 --backend-address 127.0.0.1:8080
```

You should see the output: `[Server] Listening on 127.0.0.1:8081`.

### 3. Run the Client Proxy

The client proxy listens for plaintext traffic from your application and
forwards it over the secure tunnel to the server proxy.

Run the client proxy in a third terminal:

```bash
bazel run //oak_proxy/client -- --listen-address 127.0.0.1:9090 --server-proxy-address 127.0.0.1:8081
```

You should see the output: `[Client] Listening on 127.0.0.1:9090`.

### 4. Send Traffic

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

## Testing

The proxy has an automated test that simulates the manual steps described above.
To run the test:

```bash
bazel test //oak_proxy:proxy_test
```

## Future Work

This implementation is a functional proof-of-concept. Future enhancements could
include:

- [ ] **Attestation**: Configure the `oak_session` to perform attestation,
      ensuring the proxies are running in a trusted environment.
- [ ] **Robustness**: Improve error handling and connection management for
      production use cases.
- [ ] **Packaging**: Create distributable packages for easier deployment of the
      proxies on client and server machines.
