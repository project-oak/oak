![Trusted Shuffler](..docs/oak-logo/svgs/oak-trusted-shuffler.svg?sanitize=true)

This directory contains a Trusted Shuffler example application.

Run an example with the following command:

```bash
./experimental/trusted_shuffler/scripts/run
```

## Components

### Backend

A Backend server for the Trusted Shuffler example to test and experiment. You
can switch between a simple HTTP or gRPC echo service.

Build and run the gRPC backend with the following command:

```bash
./experimental/trusted_shuffler/scripts/run_grpc_backend
```

Backend code is in the `backend` directory.

### Client

A Client that connects to the Trusted Shuffler and sends a single of request via
HTTP.

Build and run the Client with the following command:

```bash
./experimental/trusted_shuffler/scripts/run_grpc_client
```

Client code is in the `client` directory.

### Server

Proxy server that runs that collects client requests, shuffles them using the
Trusted Shuffler and sends the shuffled requests to the Backend.

Server code is in the `server` directory.

### Trusted Shuffler

Library implementation of the Trusted Shuffler logic.

Trusted Shuffler code is in the `trusted_shuffler` directory.

### Common

Library that contains an logic shared between `backend`, `server` and `client`.

Common code is in the `common` directory.
