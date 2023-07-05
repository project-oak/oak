# FROM clearlinux@sha256:88652d2682bd63208e55f069c0ca4d3c30fe3acf2c5b730d16f8099a6d437162
ARG debian_snapshot=sha256:f0b8edb2e4436c556493dce86b941231eead97baebb484d0d5f6ecfe4f7ed193
FROM debian@${debian_snapshot}

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

# Install Docker. This is a starting point only, we should switch to a more lightweight runtime later.
RUN apt-get --yes update && apt-get install --no-install-recommends --yes curl gnupg2 gnupg-agent ca-certificates
RUN curl --fail --silent --show-error --location https://download.docker.com/linux/debian/gpg | apt-key add -
RUN echo "deb [arch=amd64] https://download.docker.com/linux/debian bookworm stable"  > /etc/apt/sources.list.d/backports.list

RUN apt-get --yes update \
  && apt-get install --yes --no-install-recommends \
  systemd systemd-sysv \
  docker-ce \
  # Cleanup
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*

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

# Clean up some stuff we don't need
RUN rm -rf /usr/share/doc /usr/share/info /usr/share/man
