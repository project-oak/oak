# Use Envoy Proxy 1.19.0-alpine-dev.
FROM envoyproxy/envoy-alpine-dev:fc6099e488671ff5ec6d7c259c180890a59a9afd

COPY ./oak_functions/loader/target/x86_64-unknown-linux-musl/release/oak_functions_loader /oak_functions_loader
COPY ./experimental/oak_functions_with_envoy/server/server.yaml /server.yaml
COPY ./experimental/oak_functions_with_envoyscripts/run_server.sh /run_server.sh

ENTRYPOINT ["/etc/envoy/run_server.sh"]
