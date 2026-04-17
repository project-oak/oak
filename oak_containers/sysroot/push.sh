#!/bin/bash

# Push the bazel-built sysroot.
# This should only be called via bazel run.

set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

if [ -n "${BUILD_WORKSPACE_DIRECTORY}" ]; then
  echo "Pushing the sysroot built by bazel."
else
  echo "Use bazel run //oak_containers/sysroot:push to push the sysroot."
  exit 1
fi

readonly file=sysroot.tar.xz
readonly hash=$(sha256sum "${file}" | cut -d " " -f 1)
gsutil cp "${file}" "gs://oak-bins/sysroot/${hash}.tar.xz"
gsutil cp "${file}" "gs://oak-files/sha2-256:${hash}"
