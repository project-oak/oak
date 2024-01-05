ARG debian_snapshot=sha256:f0b8edb2e4436c556493dce86b941231eead97baebb484d0d5f6ecfe4f7ed193
FROM debian@${debian_snapshot}

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

RUN apt-get --yes update \
  && apt-get install --yes --no-install-recommends \
  systemd systemd-sysv dbus udev runc \
  # Cleanup
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*

# Clean up some stuff we don't need
RUN rm -rf /usr/share/doc /usr/share/info /usr/share/man

# Copy config files
COPY files /

# Prepare network
RUN systemctl enable systemd-networkd

# Copy the orchestartor binary & service
COPY ./target/oak_containers_orchestrator /usr/bin/oak_containers_orchestrator
RUN systemctl enable oak-orchestrator

# Log relay
COPY ./target/oak_containers_syslogd_patched /usr/bin/oak_containers_syslogd
RUN systemctl enable oak-syslogd

# Only enable interactive logins if the kernel was booted with "debug" flag.
RUN systemctl disable getty@
RUN systemctl enable root-passwd

# Don't bother starting the graphical interface, let's stick with the basic multi-user target.
RUN systemctl set-default multi-user
