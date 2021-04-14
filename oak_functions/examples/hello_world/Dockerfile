# Allow deploying the latest version for development.
# hadolint ignore=DL3007
FROM gcr.io/oak-ci/oak-functions:latest

COPY ./bin/hello_world.wasm /module.wasm
COPY ./config.toml /config.toml
