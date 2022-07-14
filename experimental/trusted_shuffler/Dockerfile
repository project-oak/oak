FROM gcr.io/distroless/base

COPY ./bin/trusted_shuffler_server /trusted_shuffler_server

ENTRYPOINT [ \
    "/trusted_shuffler_server", \
    "--backend-url=http://localhost:8888", \
    "--k=10", \
    "--listen-address=[::]:8080" \
    ]
