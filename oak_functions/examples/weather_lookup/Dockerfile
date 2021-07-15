# Use an argument to specify base image containing the Oak Functions loader.
# Default to using the latest version for development.
ARG base_image=gcr.io/oak-ci/oak-functions:latest
# hadolint ignore=DL3006
FROM ${base_image}

COPY ./bin/weather_lookup.wasm /module.wasm
COPY ./config.toml /config.toml
