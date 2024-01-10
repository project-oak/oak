# Use a fixed snapshot of the base image to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/_/debian/tags
ARG image_digest=sha256:86bfca4fe16adcf0a98b1564177130641ce576775cd443e94fadd4d76cb22cc7
FROM debian:trixie-slim@${image_digest}

RUN apt-get update && apt-get install --no-install-recommends --yes ca-certificates curl git nix

RUN echo 'experimental-features = nix-command flakes' >> /etc/nix/nix.conf

# Solves the following error when running on GitHub Actions:
#
# fatal: detected dubious ownership in repository at '/workspace'
#   To add an exception for this directory, call:
#   git config --global --add safe.directory /workspace
RUN git config --global --add safe.directory /workspace
