# FROM clearlinux@sha256:88652d2682bd63208e55f069c0ca4d3c30fe3acf2c5b730d16f8099a6d437162
ARG debian_snapshot=sha256:f0b8edb2e4436c556493dce86b941231eead97baebb484d0d5f6ecfe4f7ed193
FROM debian@${debian_snapshot}

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

RUN apt-get --yes update \
  && apt-get install --yes --no-install-recommends \
  systemd systemd-sysv dbus udev\
  # Cleanup
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*

# Prepare network
RUN systemctl enable systemd-networkd
COPY 10-enp0s1.network /etc/systemd/network
RUN chmod 644 /etc/systemd/network/10-enp0s1.network

# Copy the orchestartor binary & service
COPY ./target/oak_containers_orchestrator /usr/bin/
COPY oak-orchestrator.service /etc/systemd/system/
RUN chmod 644 /etc/systemd/system/oak-orchestrator.service

# Start the orchestartor at boot
RUN systemctl enable oak-orchestrator

# Override the default journald configuration
COPY journald.conf /etc/systemd/journald.conf.d/clear.conf

# Only enable interactive logins if the kernel was booted with "debug" flag.
COPY serial-getty@.override.conf /etc/systemd/system/serial-getty@.service.d/override.conf
RUN systemctl disable getty@
COPY root-passwd.service /etc/systemd/system
RUN chmod 644 /etc/systemd/system/root-passwd.service
RUN systemctl enable root-passwd

# Don't bother starting the graphical interface, let's stick with the basic multi-user target.
RUN systemctl set-default multi-user

# Clean up some stuff we don't need
RUN rm -rf /usr/share/doc /usr/share/info /usr/share/man
