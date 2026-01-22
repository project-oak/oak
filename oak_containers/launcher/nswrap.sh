#!/bin/bash
#
# Convenience script to set up networking in a network namespace for tests.

set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

ip link set lo up

TAP="oak0"
HOSTADDR="10.0.2.100/24"
HOSTADDR_6="fdd2:a994:f3c5:1:10:0:2:64/64"

ip tuntap add dev $TAP mode tap
ip addr flush dev $TAP
ip addr add $HOSTADDR dev $TAP
ip addr add $HOSTADDR_6 dev $TAP
ip link set dev $TAP up

exec "$@"
