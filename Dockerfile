# Use fixed digest of the base image to create a deterministic environment.
# Digests can be found at https://hub.docker.com/r/nixpkgs/nix/tags
ARG base_image_digest=sha256:f554defc0aee632ad43fc20e37da658bfdfa9112a1f951cdafbafeb8c3732330
FROM nixpkgs/nix@${base_image_digest}

RUN chmod -R 777 /

ENV PATH=/root/.nix-profile/bin:$PATH

RUN mkdir /etc/nix && echo 'experimental-features = nix-command flakes' >> /etc/nix/nix.conf

RUN nix-env -iA cachix -f https://cachix.org/api/v1/install
RUN cachix use oak
