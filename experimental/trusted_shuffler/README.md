# Trusted Shuffler Example

This directory contains a Trusted Shuffler example application.

Run example with the following command:

```bash
./experimental/trusted_shuffler/scripts/run
```

## Components

### Backend

Backend server for the Trusted Shuffler example.

Backend is used in tests/experiments and is represented as a simple HTTP echo
service.

Build and run the Backend with the following command:

```bash
./experimental/trusted_shuffler/scripts/run_backend
```

Backend code is in the `backend` directory.

### Client

Client that connects to the Trusted Shuffler and sends a number of requests via
HTTP.

Build and run the Client with the following command:

```bash
./experimental/trusted_shuffler/scripts/run_client
```

Client code is in the `client` directory.

### Server

Proxy server that runs that collects Client HTTP requests, shuffles them using
the Trusted Shuffler and sends the shuffled requests to the Backend.

Build and run the Server with the following command:

```bash
./experimental/trusted_shuffler/scripts/run_server
```

Server code is in the `server` directory.

### Trusted Shuffler

Library implementation of the Trusted Shuffler logic.

Trusted Shuffler code is in the `trusted_shuffler` directory.

### Common

Library that contains an HTTP logic shared between `backend`, `server` and
`client`.

Common code is in the `common` directory.
