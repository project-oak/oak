# Holds the Trusted Shuffler.
# 
# To run locally:
# $ docker run -it -e BACKEND_URL="http://localhost:8888" -e K="1" -e LISTEN_ADDRESS="[::]:8080" --network=host gcr.io/oak-ci/trusted-shuffler
ARG debian_snapshot=sha256:fb7e04be4c79a9eab9c259fd5049f4a1bec321843040184a706bbecdaaacbd32
FROM debian/snapshot@${debian_snapshot}

COPY ./bin/trusted_shuffler_server /trusted_shuffler_server

# Ignoring the linter to use JSON notation, because with JSON notation 
# the environment variables $K, $BACKEND_URL, and $LISTEN_ADDRESS are not expanded,
# and environment variables are the way we give (and modify) the arguments
# on Google Cloud Run.
# 
# hadolint ignore=DL3025
ENTRYPOINT /trusted_shuffler_server \
    --backend-url="${BACKEND_URL}" \
    --k="${K}" \
    --listen-address="${LISTEN_ADDRESS}"
