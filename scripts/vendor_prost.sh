#!/usr/bin/env bash

readonly SCRIPTS_DIR="$(dirname "$0")"
# shellcheck source=scripts/common
source "${SCRIPTS_DIR}/common"

# Updates our local copy of https://github.com/danburkert/prost and applies a small patch to add
# support for the message_type field option.

# Master branch as of 2020-06-05
readonly PROST_COMMIT="80256277997975948d257faf3f35c2890bf12787"
readonly PROST_ZIP_SHA256="02c086f2d1b7aad110745ac701f001618cd8343f882fc9ce034aa007c4c53773"

readonly PROST_ZIP_URL="https://github.com/danburkert/prost/archive/${PROST_COMMIT}.zip"
readonly PROST_ZIP_PREFIX="prost-${PROST_COMMIT}"

# Make sure we run in the third_party directory.
cd "${SCRIPTS_DIR}/../third_party" || exit

# Download the prost zip only if it does not yet exist in the filesystem.
if [[ ! -f "${PROST_ZIP_PREFIX}.zip" ]]; then
    curl --location "${PROST_ZIP_URL}" > "${PROST_ZIP_PREFIX}.zip"
fi

# Make sure the SHA256 checks out
echo "${PROST_ZIP_SHA256} ${PROST_ZIP_PREFIX}.zip" | sha256sum --check -

# Clean up from previous runs
rm -rf "${PROST_ZIP_PREFIX}" prost/

# Unzip and move into the vendored directory (stripping the prefix).
unzip "${PROST_ZIP_PREFIX}.zip"
mv "${PROST_ZIP_PREFIX}" prost

# We do not need the bundled protobuf because we already require users to have it installed.
rm -r prost/prost-build/third-party

(
  # Apply any local patches.
  cd prost/ || exit
  for patchfile in ../prost-*.patch; do
    patch --strip=1 < "$patchfile"
  done

  # Check the local version runs, which also regenerates Cargo.lock.
  PROTOC=protoc cargo test
)
