ARG debian_snapshot=sha256:f0b8edb2e4436c556493dce86b941231eead97baebb484d0d5f6ecfe4f7ed193
FROM debian@${debian_snapshot}

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

# Install debian packages, pinning to the same snapshot as the base image.
# This takes advantage of the fact that the base image contains the snapshot
# URL as a comment in /etc/apt/sources.list.d/debian.sources, with a switch
# to snapshot-cloudflare in case it has higher availability.
RUN sed -i -e '/^URIs/d' \
    -e '/^# http:\/\/snapshot/{s/#/URIs:/;s/snapshot/snapshot-cloudflare/}' \
    -e '/^Signed-By/a\Check-Valid-Until: no' \
    /etc/apt/sources.list.d/debian.sources
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

# Enable the two Oak services
# They don't exist yet in this image, but the symlinks will be properly created.
RUN systemctl enable oak-orchestrator
RUN systemctl enable oak-syslogd

# Only enable interactive logins if the kernel was booted with "debug" flag.
RUN systemctl disable getty@
RUN systemctl enable root-passwd

# Don't bother starting the graphical interface, let's stick with the basic multi-user target.
RUN systemctl set-default multi-user
