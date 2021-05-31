# Java gRPC Attestation Client

This in the Java version of the gRPC Attestation client. It negotiates a
Diffie-Hellman key with the server and uses it to encrypt data in gRPC requests
with AES-GCM.

It's important to note that for each new gRPC request both client and server
negotiate new a session key.

Build and run client with the following command:

```bash
bazel run //oak_functions/examples/weather_lookup/client/java:client
```

Build and run gRPC Attestation example (including server) with the following
command:

```bash
./scripts/runner run-functions-examples --example-name=weather_lookup --client-variant=java
```
