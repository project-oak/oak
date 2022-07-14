FROM gcr.io/distroless/static@sha256:73c8aadbd4ca392807a8707944cd94098f4336e2a74a96a1c4e94e5bf4546570

COPY ./bin/trusted_shuffler_server /trusted_shuffler_server

ENTRYPOINT [ \
    "/trusted_shuffler_server", \
    "--backend-url=http://localhost:8888", \
    "--k=10", \
    "--listen-address=[::]:8080" \
    ]
