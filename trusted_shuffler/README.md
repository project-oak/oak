<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-trusted-shuffler-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-trusted-shuffler.svg?sanitize=true"><img alt="Project Oak Trusted Shuffler Logo" src="/docs/oak-logo/svgs/oak-trusted-shuffler.svg?sanitize=true"></picture></h1>
<!-- Oak Trusted Shuffler Logo End -->

This directory contains a Trusted Shuffler example application.

Run an example with the following command:

```bash
./trusted_shuffler/scripts/run
```

## Components

### Backend

A Backend server for the Trusted Shuffler example to test and experiment. You
can switch between a simple HTTP or gRPC echo service.

Build and run the gRPC backend with the following command:

```bash
./trusted_shuffler/scripts/run_grpc_backend
```

Backend code is in the `backend` directory.

### Client

A Client that connects to the Trusted Shuffler and sends a single of request via
gRPC.

Build and run the Client with the following command:

```bash
./trusted_shuffler/scripts/run_grpc_client
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

### Deploy a Trusted Shuffler on Google Cloud

Build the Docker image running the Server with:

```bash
./trusted_shuffler/scripts/docker_build
```

Deploy on [Google Cloud](https://pantheon.corp.google.com/run?project=oak-ci)
with:

```bash
./trusted_shuffler/scripts/deploy_on_google_cloud
```

Make sure to set the environment variable `BACKEND_URL` to your backend. You can
also modify the environment variables once deployed.

### Run a Trusted Shuffler on a local machine

Use the Oak Docker container (everything you need is installed in there):

```bash
./scripts/docker_sh
```

In the Oak Docker container run:

```bash
./trusted_shuffler/scripts/run_trusted_shuffler
```
