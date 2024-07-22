# Use a fixed snapshot of the base image to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/_/debian/tags
ARG image_digest=sha256:f528891ab1aa484bf7233dbcc84f3c806c3e427571d75510a9d74bb5ec535b33
FROM debian:bookworm-slim@${image_digest}

RUN apt-get update && apt-get install --no-install-recommends --yes ca-certificates curl git xz-utils nix

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
