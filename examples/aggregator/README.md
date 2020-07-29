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
export RUST_LOG=info
cargo run --release --manifest-path=examples/aggregator/backend/Cargo.toml -- \
  --grpc-tls-private-key=./examples/certs/local/local.key \
  --grpc-tls-certificate=./examples/certs/local/local.pem
```

Backend code is in the `backend` directory.

### Aggregator

Aggregator example for Project Oak.

This application shows how an Oak Node can aggregate data samples and report
aggregated values if there are enough samples to hide individual contributors
(enforces k-anonymity).

Clients invoke the module by providing data samples that contain a bucket ID and
a Sparse Vector - a dictionary with integer keys.

Build and run the Aggregator with the following command:

```bash
./scripts/runner run-examples --client-variant=none --example-name=aggregator
```

Aggregator code is in `common` and `module` directories (where `common` defines
a generic Aggregator data structure).

### Client

Simple client that connects to the Aggregator and sends a data sample via gRPC.

Build and run the Client with the following command:

```bash
./scripts/runner run-examples --run-server=false --example-name=aggregator
```

A common use case is to keep running the client until the aggregation threshold
is reached, at which point the aggregator should release the aggregated data to
the backend over gRPC.

Client code is in the `client` directory.

## Deployment

The Aggregator example contains a `gcp/deployment.yaml` file which is a config
for Google Cloud deployment.

Each pod in an Aggregator deployment consists of two running containers, namely
an Aggregator Oak application and a Backend server. In addition, the Aggregator
deployment exposes a service externally with a TCP Load Balancer and an assigned
static IP that listens on the port `8080`. Aggregator is deployed using
[Kubernetes](https://kubernetes.io/).

In order to deploy the Aggregator example - first set up Kubernetes:

```bash
gcloud components install kubectl
```

and then run the following command:

```bash
./examples/aggregator/scripts/deploy
```

And the command for deleting the Aggregator example from Google Cloud looks as
follows:

```bash
./examples/aggregator/scripts/undeploy
```

For both commands, use the `-m` flag to deploy or undeploy the
`metrics-sidecar`.

Deployment requires Docker images to be uploaded to the
[Cloud Container Registry](http://gcr.io/oak-ci/) (requires write-access) with
the following command:

```bash
./examples/aggregator/scripts/docker_build_and_push
```

## Monitoring

Run the following command to create a monitoring dashboard with charts showing
memory and CPU usage, as well as application specific metrics. It also creates a
simple alert policy to check that at least one instance of the aggregator is
running.

```bash
./examples/aggregator/scripts/monitoring
```

Dashboards can be created and modified using the web interface. The updated
`json` file can be fetched using the command:

```bash
gcloud monitoring dashboards describe [DASHBOARD-ID] --format=json > aggregator-dashboard.json
```

where `DASHBOARD-ID` is of the form
`projects/121212121212/dashboards/16161616161616167`, and can be found in the
output from

```bash
gcloud monitoring dashboards list
```
