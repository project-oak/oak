#!/bin/bash
set -o errexit
set -o pipefail
set -o nounset
set -o xtrace

# Externally provided env variables:
# INSTANCE_NAME
# ZONE

gcloud compute instances reset "${INSTANCE_NAME}" --zone="${ZONE}"
