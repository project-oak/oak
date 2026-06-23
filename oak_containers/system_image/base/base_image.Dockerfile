# System Image for Oak Containers. Contains base Debian plus binaries and
# configs to run Oak. This MUST be based on a stable Debian image.
# debian:stable-20260610-slim - https://hub.docker.com/_/debian/tags
#
# Note; if you change this version, you should change the sysroot version in
# oak_containers/sysroot/sysroot.yaml and the app_base version  in
# oak_containers/app_base/app_base.yaml to match.
ARG debian_snapshot=sha256:34363c20bd149e41365fc77b086da067ed13ab2dff4cd0612788e12e6d52c44c
FROM debian@${debian_snapshot}

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

RUN apt-get --yes update \
    && apt-get install --yes --no-install-recommends \
    systemd systemd-sysv dbus udev runc \
    # Cleanup
    && apt-get clean \
    && rm --recursive --force /var/lib/apt/lists/*

# Clean up several non-deterministic and unneeded files:
#  * /etc/shadow contains the date passwords were generated; set to the same
#    age as root
#  * passwd and shadow backup files can be removed
#  * /var/lib/dbus/machine-id can be a symlink to /etc/machine-id
#  * /etc/machine-id should be missing or empty so that it's generated on boot
#  * various log files can be empty
#  * doc/info/man pages aren't needed
#  * /var/cache/ldconfig/aux-cache can be removed; this is safe for all files
#    in /var/cache
RUN (LAST_DAY="$(awk -F: '$1=="root"{print $3}' /etc/shadow)"; \
    chage -d "$LAST_DAY" messagebus && chage -d "$LAST_DAY" systemd-network) \
    && rm -f /etc/{passwd,shadow}- \
    && ln -sf /etc/machine-id /var/lib/dbus/machine-id \
    && find /etc/machine-id /var/log -type f -execdir truncate -s 0 '{}' '+' \
    && rm -rf /usr/share/{doc,info,man} /var/cache/ldconfig/aux-cache

# Copy config files
COPY --chmod=0755 files /

# Prepare network
RUN systemctl enable systemd-networkd

# Enable the two Oak services
# They don't exist yet in this image, but the symlinks will be properly created.
RUN systemctl enable oak-orchestrator
RUN systemctl enable oak-syslogd
RUN systemctl enable oak-agent

# Only enable interactive logins if the kernel was booted with "debug" flag.
RUN systemctl disable getty@
RUN systemctl enable root-passwd

# Don't bother starting the graphical interface, let's stick with the basic multi-user target.
RUN systemctl set-default multi-user
