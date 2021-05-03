# Envoy Proxy Experiment

This experiment shows how to create a persistent connection to a Docker
container in Cloud Run. It is done by using
[TCP tunneling over HTTP](https://www.envoyproxy.io/docs/envoy/latest/intro/arch_overview/http/upgrades#tunneling-tcp-over-http)
in Envoy proxy.

The experiment consists of 2 Envoy proxies: _client side_ and _server side_.

- Client side proxy accepts TCP streams and tunnels them over HTTP streams.
- Server side proxy listens for HTTP streams and unwraps TCP streams from them.

Proxy experiment is organized as follows:

- `curl`
  - Sends an HTTP GET request on `localhost:8000`
- `client_listener`
  - Tunnels TCP stream over HTTP/2 stream
- `client_cluster`
  - Sends HTTP/2 stream on `APP_URL:443` using TLS
  - Checks Google public certificate
- Cloud Run Frontend
  - Terminates TLS connection
  - Redirects HTTP/2 stream to the Docker container on port `8080`
- `server_listener`
  - Unwraps a TCP stream from an HTTP/2 stream
- `server_cluster`
  - Forwards TCP stream to the server on port `8081`
- `python` server
  - Responds to an HTTP GET request

## Running experiment

Build Docker images:

```bash
./experimental/envoy_proxy/scripts/build.sh
```

### Running on localhost

Run the server:

```bash
docker run -it --network='host' 'gcr.io/oak-ci/envoy-proxy-example-server'
```

Run the client:

```bash
docker run -it --network='host' 'gcr.io/oak-ci/envoy-proxy-example-client' localhost
```

### Running in Cloud Run

Export environment variables (the corresponding JSON key can be created in
[GCP console](https://pantheon.corp.google.com/iam-admin/serviceaccounts/details/107443053308787082748/keys?project=oak-ci)):

```bash
export GCP_PROJECT_ID=oak-ci
export GCP_ACCOUNT_FILE=${JSON_KEY_PATH}
```

Deploy the server:

```bash
./experimental/envoy_proxy/scripts/deploy.sh
```

Run the client:

```bash
docker run -it --network='host' 'gcr.io/oak-ci/envoy-proxy-example-client'
```

Delete the server (_optional_):

```bash
./experimental/envoy_proxy/scripts/delete.sh
```
