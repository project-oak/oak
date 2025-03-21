#!/bin/bash
#
# Builds and uploads one of the base image variants.
#
set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

readonly SCRIPTS_DIR="$(dirname "$0")"
readonly TARGET_DIR=oak_containers/system_image/base/target

usage_and_exit() {
  set +o xtrace

  >&2 echo "Usage: $0 [vanilla|nvidia|sysroot]"
  >&2 echo "Builds and pushes one of the containers base images."
  >&2 echo ""
  >&2 echo "If you haven't done a push before, you'll need to set up gcloud."
  >&2 echo "Install gcloud if needed: https://cloud.google.com/sdk/docs/downloads-interactive"
  >&2 echo "And then:"
  >&2 echo "  gcloud auth login"
  >&2 echo "  gcloud config set project oak-ci"
  >&2 echo "  gcloud auth configure-docker"
  >&2 echo "  gcloud auth configure-docker europe-west2-docker.pkg.dev"

  exit 1
}

if [[ $# != 1 ]]; then
  usage_and_exit
fi
if [ "$1" == "vanilla" ]; then
  "${SCRIPTS_DIR}/build-base.sh" vanilla
  readonly source=base-image.tar
  readonly static_dir=base-image
elif [ "$1" == "nvidia" ]; then
  "${SCRIPTS_DIR}/build-base.sh" nvidia
  readonly source=nvidia-base-image.tar
  readonly static_dir=nvidia-base-image
elif [ "$1" == "sysroot" ]; then
  "${SCRIPTS_DIR}/build-base.sh" sysroot
  readonly source=sysroot.tar
  readonly static_dir=sysroot
else
  usage_and_exit
fi

xz --force "${TARGET_DIR}/${source}"
file="${TARGET_DIR}/${source}.xz"
hash=$(sha256sum "${file}" | cut -d " " -f 1)
# TODO: b/399705292 - In WORKSPACE, read from oak-files not from oak-bins.
gsutil cp "${file}" "gs://oak-bins/${static_dir}/${hash}.tar.xz"
gsutil cp "${file}" "gs://oak-files/sha2-256:${hash}"
