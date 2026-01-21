#!/bin/bash
#
# Copyright 2026 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

#
# Downloads the Debian 12 "nocloud" base image for VM benchmarks.
# Verifies the image hash for reproducibility.
#

set -o errexit
set -o nounset
set -o pipefail

IMAGE_NAME="debian-12-nocloud-amd64.qcow2"
IMAGE_URL="https://cloud.debian.org/images/cloud/bookworm/latest/${IMAGE_NAME}"

# SHA512 hash for verification (from https://cloud.debian.org/images/cloud/bookworm/latest/SHA512SUMS)
# To update: curl -sL https://cloud.debian.org/images/cloud/bookworm/latest/SHA512SUMS | grep nocloud-amd64
EXPECTED_SHA512="90a54bffd469a81656128ddff931e170d61d75888ba92e5b28ab73a1f08626361d2ba18bc20aec94c8aebad531259b78e8ab21107f652683db4cdd9dd367fd80"

# Default output location.
OUTPUT_DIR="${1:-$(pwd)}"
OUTPUT_FILE="${OUTPUT_DIR}/${IMAGE_NAME}"

usage() {
    cat <<EOF
Usage: $0 [output_directory]

Downloads the Debian 12 nocloud base image for use with create_image.sh.

Arguments:
  output_directory    Where to save the image (default: current directory)

Example:
  $0 ~/Downloads
EOF
    exit 1
}

if [[ "${1:-}" == "--help" ]] || [[ "${1:-}" == "-h" ]]; then
    usage
fi

# Create output directory if needed.
mkdir -p "${OUTPUT_DIR}"

echo "Downloading ${IMAGE_NAME}..."
echo "  URL:    $IMAGE_URL"
echo "  Output: $OUTPUT_FILE"
echo ""

# Download image.
if ! command -v wget &> /dev/null; then
    echo "Error: wget not found"
    exit 1
fi
wget -O "${OUTPUT_FILE}" "${IMAGE_URL}"

# Verify checksum.
echo ""
echo "Verifying SHA512 checksum..."

ACTUAL_SHA512=$(sha512sum "${OUTPUT_FILE}" | awk '{print $1}')

if [[ "${EXPECTED_SHA512}" == "${ACTUAL_SHA512}" ]]; then
    echo "  ✓ Checksum verified"
else
    echo "  ✗ Checksum mismatch!"
    echo "    Expected: ${EXPECTED_SHA512}"
    echo "    Actual:   ${ACTUAL_SHA512}"
    echo ""
    echo "The image may have been updated. To get the new hash:"
    echo "  curl -sL https://cloud.debian.org/images/cloud/bookworm/latest/SHA512SUMS | grep nocloud-amd64"
    rm "${OUTPUT_FILE}"
    exit 1
fi

echo ""
echo "Done! Image saved to: ${OUTPUT_FILE}"
echo ""
echo "Next steps:"
echo "  ./oak_benchmarks/linux_vm/prepare_image.sh --base-image=${OUTPUT_FILE} --binary=<your_app> --output=/tmp/vm.qcow2"
