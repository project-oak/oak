# TLS-over-gRPC Demonstration

This is a simple example showing a bare-bones server/client pair that can
establish a TLS session using a gRPC bidirectional streaming session as the
underlying channel.

To run the server: `bazel run experiments/tls-over-grpc:server`

The server will accept new bidirectional stream invocations. Each new invocation
starts a new TLS session. Once the session is established, any number of
messages can be sent, and the server will resond.

To run run the client: `bazel run experiments/tls-over-grpc:client`

The client performs the handshake sequence, and then sends a single message
before closing.

You can also run the provided test to verify the behavior in one command:
`bazel test experiments/tls-over-grpc:client-server-test`:w
