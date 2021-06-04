# Allow deploying the latest version for development.
# hadolint ignore=DL3007
FROM gcr.io/oak-ci/oak-functions:latest

COPY ./bin/weather_lookup.wasm /module.wasm
COPY ./config.toml /config.toml
