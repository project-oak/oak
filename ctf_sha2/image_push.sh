#!/bin/bash
set -o errexit
set -o pipefail
set -o nounset
set -o xtrace

# Externally provided env variables:
# IMAGE_URL
readonly IMAGE_FOLDER="$1"

# TODO: b/437834944 - Generalize this script.
# TODO: b/437879527 - Consider using standard bazel rules for this.
gcrane push "${IMAGE_FOLDER}" "${IMAGE_URL}"
