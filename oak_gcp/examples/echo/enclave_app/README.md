<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-containers-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"><img alt="Project Oak Containers Logo" src="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Example Encrypted Echo App

This standalone example uses a Noise Protocol end-to-end encrypted session over
gRPC.

To run this example locally in a docker container use:

```bash
bazel run //oak_gcp/examples/echo/enclave_app:echo_enclave_app_push
docker run --publish 8080:8080 \
    --rm --init \
    europe-west2-docker.pkg.dev/oak-ci/example-enclave-apps/echo_enclave_app:latest
```

Note: pushing the image requires authenticating with gcloud:

```bash
gcloud auth login
gcloud config set project oak-ci
gcloud auth configure-docker
gcloud auth configure-docker europe-west2-docker.pkg.dev
```

Once the app is running it can be tested from another shell using:

```bash
bazel run //oak_gcp/examples/echo/client:bin/oak_gcp_examples_echo_client -- \
    --request='test message'
```
