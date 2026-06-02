# Docker image we use to run CI. Build with scripts/docker_build.
# Open a shell to this image with scripts/docker_sh.
# Use a fixed snapshot of the base image to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/_/debian/tags
ARG image_digest=sha256:5012d0517aa0075a7150a45aae67586641e898913b7af3b08228108565b5f90c
FROM debian:stable-slim@${image_digest}

# We need unzip for rules_android, which doesn't seem to find unzip in the nix path
RUN apt-get update && apt-get install --no-install-recommends --yes ca-certificates curl git xz-utils unzip nix

RUN echo 'experimental-features = nix-command flakes' >> /etc/nix/nix.conf

# Make nix use the default profile for the current user.
ENV PATH=/nix/var/nix/profiles/default/bin/:$PATH

# Install cachix.
RUN nix profile install --accept-flake-config nixpkgs#cachix

# The USER variable must be set for cachix to work.
ENV USER=root

# Use oak cache by default.
RUN cachix use oak-1

# Solves the following error when running on GitHub Actions:
#
# fatal: detected dubious ownership in repository at '/workspace'
#   To add an exception for this directory, call:
#   git config --global --add safe.directory /workspace
RUN git config --global --add safe.directory /workspace
