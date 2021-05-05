# Use Envoy Proxy 1.19.0-dev.
FROM envoyproxy/envoy-dev:22825906e35c1d61b495f7b5f2517249cc56f77d

COPY ./server/server.yaml /server.yaml
COPY ./scripts/run_server.sh /run_server.sh
COPY ./bin/oak_functions_loader /oak_functions_loader
COPY ./bin/weather_lookup.wasm /module.wasm
COPY ./bin/config.toml /config.toml

ENTRYPOINT ["/run_server.sh"]
