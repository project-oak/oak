#!/bin/bash
set -o errexit
set -o pipefail
set -o nounset
set -o xtrace

# Externally provided env variables:
# IMAGE_URL
# INSTANCE_NAME
# ZONE

readonly IMAGE_DIGEST_FILE="$1"
readonly IMAGE_SHA256="$(cat "${IMAGE_DIGEST_FILE}")"
# TODO: b/437834944 - Generalize this script.
readonly IMAGE_DIGEST="${IMAGE_URL}@${IMAGE_SHA256}"
gcloud compute instances create "${INSTANCE_NAME}" \
    --shielded-secure-boot \
    --confidential-compute-type=TDX \
    --image-project=confidential-space-images \
    --image-family=confidential-space \
    --maintenance-policy=TERMINATE \
    --scopes=cloud-platform \
    --zone="${ZONE}" \
    --metadata="^~^tee-image-reference=${IMAGE_DIGEST}~tee-container-log-redirect=true"
