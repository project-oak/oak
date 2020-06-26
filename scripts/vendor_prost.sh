#!/bin/bash

# Vendors https://github.com/danburkert/prost and applies a small patch to add 
# support for the message_type field option.
# Add -c to create a pristine commit without the patch applied.

readonly SCRIPTS_DIR="$(dirname "$0")"
# shellcheck source=scripts/common
source "${SCRIPTS_DIR}/common"

patch=true
while getopts "hc" opt; do
  case "${opt}" in
    h)
      echo -e "Usage: ${0} [-h] [-c] 

Vendors https://github.com/danburkert/prost and applies a small patch to add 
support for the message_type field option.

Options:
  -c    Do not apply the patch, create a clean checkout instead.
  -h    Print Help (this message) and exit"
      exit 0;;
    c)
      patch=false;;
    *)
      echo "Invalid argument: ${opt}"
      exit 1;;
  esac
done

# Master branch as of 2020-06-11
readonly PROST_ZIP_URL="https://github.com/danburkert/prost/archive/80256277997975948d257faf3f35c2890bf12787.zip"
readonly PROST_ZIP_SHA256="02c086f2d1b7aad110745ac701f001618cd8343f882fc9ce034aa007c4c53773"
readonly PROST_ZIP_PREFIX="prost-80256277997975948d257faf3f35c2890bf12787"
readonly PATCH_FILE="prost-0001-Patch-to-generate-typesafe-Sender-and-Receiver.patch"

readonly THIRD_PARTY_DIR="${SCRIPTS_DIR}/../third_party"
readonly PROST_DIR="${SCRIPTS_DIR}/../third_party/prost"
readonly PROST_ZIP_FILE="${THIRD_PARTY_DIR}/${PROST_ZIP_PREFIX}.zip"

# Download prost
curl -L "$PROST_ZIP_URL" -o "${PROST_ZIP_FILE}"

# Make sure the SHA256 checks out
echo "${PROST_ZIP_SHA256} ${PROST_ZIP_FILE}" | sha256sum -c -

# Clean up from previous runs
rm -rf "${THIRD_PARTY_DIR:?}/${PROST_ZIP_PREFIX}" "${PROST_DIR}"

# Unzip and move into third_party/prost.
unzip -q "${PROST_ZIP_FILE}" -d "${THIRD_PARTY_DIR}"
mv "${THIRD_PARTY_DIR}/${PROST_ZIP_PREFIX}" "${PROST_DIR}"

# We do not need the bundled protobuf because we already require users to have it installed.
rm -r "${PROST_DIR}/prost-build/third-party"

if [ "${patch}" = true ]; then
  # Apply the patch
  patch -p1 -d "${PROST_DIR}" < "${THIRD_PARTY_DIR}/${PATCH_FILE}"
fi

# Remove the downloaded zip file
rm "${PROST_ZIP_FILE}"
