# Use an argument to specify container identifier.
# Default to using the latest version for development.
ARG container_identifier=:latest
# hadolint ignore=DL3006
FROM gcr.io/oak-ci/oak-functions${container_identifier}

COPY ./bin/weather_lookup.wasm /module.wasm
COPY ./config.toml /config.toml
