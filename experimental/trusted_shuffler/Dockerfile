# Holds the Trusted Shuffler.
# 
# To run locally:
# $ docker run --network=host gcr.io/oak-ci/trusted-shuffler
FROM gcr.io/distroless/static:latest

COPY ./bin/trusted_shuffler_server /trusted_shuffler_server

ENTRYPOINT [ \
    "/trusted_shuffler_server", \
    "--backend-url=http://localhost:8888", \
    "--k=1", \
    "--listen-address=[::]:8080" \
    ]
