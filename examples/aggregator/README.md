# Aggregator Example

This directory holds an Aggregator application.

## Components

### Backend

Backend server for the Aggregator example.

Backend is used in tests/experiments and is represented as a gRPC server that
listens for samples provided by the Aggregator and prints them into the standard
output.

Build and run the Backend with the following command:

```bash
cargo run --release --package=aggregator_backend
```

Backend code is in the `backend` directory.

### Client

Simple client that connects to the Aggregator and sends a data sample via gRPC.

Build and run the Client with the following command:

```bash
./scripts/build_example -e aggregator
./bazel-client-bin/examples/aggregator/client/client --address=127.0.0.1 --bucket=test --data=1:10,2:20,3:30
```

Client code is in the `client` directory.

### Aggregator

Aggregator example for Project Oak.

This application shows how an Oak Node can aggregate data samples and report
aggregated values if there are enough samples to hide individual contributors
(enforces k-anonymity).

Clients invoke the module by providing data samples that contain a bucket ID and
a Sparse Vector - a dictionary with integer keys.

Build and run the Aggregator with the following command:

```bash
./scripts/build_server -s asylo
./bazel-bin/oak/server/asylo/asylo_oak_runner --application=./bazel-client-bin/examples/aggregator/config/config.bin
```

Aggregator code is in `common` and `module` directories (where `common` defines
a generic Aggregator data structure).

## Deployment

The Aggregator example contains a `gcp/pod.yaml` file which is a config for
Google Cloud deployment.

An Aggregator deployment consists of a single pod with two running containers
(an Aggregator Oak application and a Backend server) and a service with a TCP
Load Balancer and an assigned static IP that listens on the port `8080`.
Aggregator is deployed using [Kubernetes](https://kubernetes.io/).

In order to deploy the Aggregator example - run:

```bash
./examples/aggregator/scripts/deploy
```

And the command for deleting the Aggregator example from Google Cloud looks as
follows:

```bash
./examples/aggregator/scripts/undeploy
```

Deployment requires Docker images to be uploaded to the
[Cloud Container Registry](gcr.io/oak-ci/) (requires write-access) with the
following command:

```bash
./examples/aggregator/scripts/build_docker_images
./examples/aggregator/scripts/docker_push
```
