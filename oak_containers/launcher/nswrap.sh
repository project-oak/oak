 #!/bin/bash
#
# Convenience script to set up networking in a network namespace for tests.

set -e

ip link set lo up

TAP="oak0"
HOSTADDR="10.0.2.100/24"

ip tuntap add dev $TAP mode tap
ip addr flush dev $TAP
ip addr add $HOSTADDR dev $TAP
ip link set dev $TAP up

exec "$@"
