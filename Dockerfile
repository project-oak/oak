# Use fixed snapshot of Debian to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/r/nixos/nix/tags
ARG nix_snapshot=sha256:fd80e5ebe77a7737517ae55fbc08db623814e875ebe4e154e9954f7177560acc
FROM nixos/nix@${nix_snapshot}

RUN echo 'experimental-features = nix-command flakes' >> /etc/nix/nix.conf

RUN nix-env -iA cachix -f https://cachix.org/api/v1/install
RUN cachix use oak

# Solves the following error when running on GitHub Actions:
#
# fatal: detected dubious ownership in repository at '/workspace'
#   To add an exception for this directory, call:
#   git config --global --add safe.directory /workspace
RUN git config --global --add safe.directory /workspace
