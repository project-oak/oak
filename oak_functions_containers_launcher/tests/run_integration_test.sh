#!/bin/bash
set -e

# We need a new network namespace so that we could create a `oak0` TAP device for the test.
# We also need to map ourselves to root in the new namespace so that we could actually configure
# that device.
# The actual device creation (and configuration) is in the `nswrap.sh` script.
unshare --map-root-user --net "${RUNFILES_DIR}"/"${TEST_WORKSPACE}"/oak_containers/launcher/nswrap.sh "$1"
