FROM gcr.io/distroless/static@sha256:d2b0ec3141031720cf5eedef3493b8e129bc91935a43b50562fbe5429878d96b

ARG oak_functions_loader_path=/oak_functions_loader

COPY ./loader/target/x86_64-unknown-linux-musl/release/oak_functions_loader ${oak_functions_loader_path}

# We cannot use ARG values as part of ENTRPOINT, so we have to repeat them here.
# https://docs.docker.com/engine/reference/builder/#environment-replacement
#
# Normally we would use the $PORT env variable here, but since we do not have a shell available in
# the Docker image, we hardcode its default value (8080) here.
# https://cloud.google.com/run/docs/reference/container-contract#port
ENTRYPOINT [ \
    "/oak_functions_loader", \
    "--http-listen-port=8080", \
    "--wasm-path=/module.wasm", \
    "--config-path=/config.toml" \
    ]

# Individual applications must copy their own Wasm module to `/module.wasm` and their config file to
# `/config.toml`.
