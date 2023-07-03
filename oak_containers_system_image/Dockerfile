FROM clearlinux@sha256:88652d2682bd63208e55f069c0ca4d3c30fe3acf2c5b730d16f8099a6d437162

# Remove .dockerenv as we will not run this image in an actual Docker container.
RUN rm /.dockerenv

# Install Clear Linux's containers-basic bundle. This gives an installation of
# docker to run containers. This is a starting point only, we should switch to
# a more lightweight runtime later.
# Ref: https://clearlinux.github.io/clear-linux-documentation/tutorials/docker.html#install-the-containers-basic-bundle
RUN swupd bundle-add containers-basic

# Configure systemd to run docker at startup
RUN systemctl enable docker

# Copy the orchestartor binary & service
COPY ./target/oak_containers_orchestrator /usr/bin/
COPY oak-orchestrator.service /etc/systemd/system/
RUN chmod 644 /etc/systemd/system/oak-orchestrator.service

# Start the orchestartor at boot
RUN systemctl enable oak-orchestrator

# Override the default journald configuration
COPY journald.conf /etc/systemd/journald.conf.d/clear.conf

# Don't bother starting the graphical interface, let's stick with the basic multi-user target.
RUN systemctl set-default multi-user

# Clean up some stuff we don't need (like the `swupd` tool itself)
RUN swupd bundle-remove trurl os-core-update os-core-webproxy
RUN rm -rf ./var/lib/swupd
