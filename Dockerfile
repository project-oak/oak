# Use fixed snapshot of Debian to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/r/debian/snapshot/tags?name=bullseye
ARG nix_snapshot=sha256:5073736c16b4c37e49786ef63c4dae7896c9994064ad0873f97c191e3a5bc335
FROM nixos/nix@${nix_snapshot}

RUN echo 'experimental-features = nix-command flakes' >> /etc/nix/nix.conf

RUN nix-env -iA cachix -f https://cachix.org/api/v1/install
RUN cachix use oak
