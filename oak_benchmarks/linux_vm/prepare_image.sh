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
# Creates a Debian VM image with an application binary pre-installed.
# Uses guestfish to inject the binary into the image before booting.
#
# For Bazel targets, use the vm_disk_image() macro in defs.bzl instead.
#

set -o errexit
set -o nounset
set -o pipefail

# Default values.
BINARY=""
BASE_IMAGE=""
OUTPUT=""
COMMAND=""
SERVICE_NAME="app"
INSTALL_PATH="/opt/app"
DATA_FILES=()
EXTRA_IP=""

usage() {
  cat <<EOF
Usage: $0 --binary=<path> --base-image=<path> --output=<path> [options]

Required:
  --binary=PATH        Path to the application binary to inject
  --base-image=PATH    Path to the Debian qcow2 base image
  --output=PATH        Path for the output image (will be overwritten)

Optional:
  --command=CMD        Command to run the binary (default: {install_path}/{binary})
  --data=PATH          Additional file to inject (can be repeated)
  --service-name=NAME  Name for the systemd service (default: app)
  --install-path=PATH  Where to install the app in the VM (default: /opt/app)
  --extra-ip=CIDR      Address to add to the guest's first non-loopback
                       interface before the service starts, e.g. 198.18.0.2/30.
                       Added alongside DHCP, not instead of it, so one image
                       serves both of run_vm.sh's network modes.

For Bazel targets, use the vm_disk_image() macro instead:

    load("//oak_benchmarks/linux_vm:defs.bzl", "vm_disk_image")
    vm_disk_image(name = "my_vm", binary = ":my_binary")

Example:
  $0 --binary=/path/to/my_app \\
     --base-image=/path/to/debian.qcow2 \\
     --output=/tmp/my-vm.qcow2 \\
     --command="/opt/app/my_app --port 5000" \\
     --data=/path/to/config.txt
EOF
  exit 1
}

# Parse arguments.
for arg in "$@"; do
  case ${arg} in
    --binary=*)
      BINARY="${arg#*=}"
      ;;
    --base-image=*)
      BASE_IMAGE="${arg#*=}"
      ;;
    --output=*)
      OUTPUT="${arg#*=}"
      ;;
    --command=*)
      COMMAND="${arg#*=}"
      ;;
    --service-name=*)
      SERVICE_NAME="${arg#*=}"
      ;;
    --install-path=*)
      INSTALL_PATH="${arg#*=}"
      ;;
    --data=*)
      DATA_FILES+=("${arg#*=}")
      ;;
    --extra-ip=*)
      EXTRA_IP="${arg#*=}"
      ;;
    --help | -h)
      usage
      ;;
    *)
      echo "Unknown argument: ${arg}"
      usage
      ;;
  esac
done

# Validate required arguments.
if [[ -z ${BINARY} ]] || [[ -z ${BASE_IMAGE} ]] || [[ -z ${OUTPUT} ]]; then
  echo "Error: Missing required arguments"
  echo ""
  usage
fi

# Expand tilde in paths if HOME is set.
if [[ -n ${HOME:-} ]]; then
  BINARY="${BINARY/#\~/${HOME}}"
  BASE_IMAGE="${BASE_IMAGE/#\~/${HOME}}"
  OUTPUT="${OUTPUT/#\~/${HOME}}"
fi

# Create command based on the binary name.
BINARY_BASENAME=$(basename "${BINARY}")
if [[ -z ${COMMAND} ]]; then
  COMMAND="${INSTALL_PATH}/${BINARY_BASENAME}"
fi

# Verify inputs exist.
if [[ ! -f ${BASE_IMAGE} ]]; then
  echo "Error: Base image not found: ${BASE_IMAGE}"
  exit 1
fi

if [[ ! -f ${BINARY} ]]; then
  echo "Error: Binary not found: ${BINARY}"
  exit 1
fi

# Check for required tools.
if ! command -v guestfish &>/dev/null; then
  echo "Error: guestfish not found. Install libguestfs-tools:"
  echo "  sudo apt install libguestfs-tools"
  exit 1
fi

echo "Creating VM image..."
echo "  Base image:    ${BASE_IMAGE}"
echo "  Binary:        ${BINARY}"
echo "  Output:        ${OUTPUT}"
echo "  Service:       ${SERVICE_NAME}.service"
echo "  Command:       ${COMMAND}"
if [[ -n ${EXTRA_IP} ]]; then
  echo "  Extra address: ${EXTRA_IP}"
fi
echo "  Install path:  ${INSTALL_PATH}"

# Create temporary directory for staging.
TEMP_DIR=$(mktemp -d)

cleanup() {
  rm -rf "${TEMP_DIR}"
}
trap cleanup EXIT

# Copy binary to staging.
cp "${BINARY}" "${TEMP_DIR}/${BINARY_BASENAME}"
chmod +x "${TEMP_DIR}/${BINARY_BASENAME}"

# Copy base image.
cp "${BASE_IMAGE}" "${OUTPUT}"

# The base image configures its interfaces with netplan: /etc/netplan/90-default.yaml
# matches `en*` and asks for DHCP, which systemd-networkd renders into
# /run/systemd/network/10-netplan-all-en.network. Reuse the same `all-en` ID so
# this file merges into that definition rather than creating a second one, and
# repeat the DHCP keys so the address is added to DHCP rather than replacing it.
# `optional` keeps systemd-networkd-wait-online from blocking the boot under
# --net=tap, where nothing answers DHCP.
# https://netplan.readthedocs.io/en/stable/netplan-yaml/
if [[ -n ${EXTRA_IP} ]]; then
  NETPLAN_FILE="${TEMP_DIR}/99-extra-ip.yaml"
  cat >"${NETPLAN_FILE}" <<NETPLANEOF
network:
  version: 2
  ethernets:
    all-en:
      match:
        name: en*
      dhcp4: true
      dhcp6: true
      optional: true
      addresses:
        - ${EXTRA_IP}
NETPLANEOF
fi

# Create systemd service file.
SERVICE_FILE="${TEMP_DIR}/${SERVICE_NAME}.service"
cat >"${SERVICE_FILE}" <<SERVICEEOF
[Unit]
Description=${SERVICE_NAME} service
After=network.target

[Service]
Type=simple
ExecStart=${COMMAND}
Restart=no
StandardOutput=journal
StandardError=journal

[Install]
WantedBy=multi-user.target
SERVICEEOF

# Build guestfish commands.
echo "Injecting files into VM image..."

GF_SCRIPT="${TEMP_DIR}/guestfish_commands"
cat >"${GF_SCRIPT}" <<EOF
mkdir-p ${INSTALL_PATH}
upload ${TEMP_DIR}/${BINARY_BASENAME} ${INSTALL_PATH}/${BINARY_BASENAME}
chmod 0755 ${INSTALL_PATH}/${BINARY_BASENAME}
upload ${SERVICE_FILE} /etc/systemd/system/${SERVICE_NAME}.service
ln-sf /etc/systemd/system/${SERVICE_NAME}.service /etc/systemd/system/multi-user.target.wants/${SERVICE_NAME}.service
EOF

# netplan ignores, and warns about, a file that is group- or world-readable.
if [[ -n ${EXTRA_IP} ]]; then
  cat >>"${GF_SCRIPT}" <<EOF
upload ${NETPLAN_FILE} /etc/netplan/99-extra-ip.yaml
chmod 0600 /etc/netplan/99-extra-ip.yaml
EOF
fi

# Add data files to guestfish commands.
for data_file in "${DATA_FILES[@]}"; do
  data_basename=$(basename "${data_file}")
  echo "upload ${data_file} ${INSTALL_PATH}/${data_basename}" >>"${GF_SCRIPT}"
done

# Execute guestfish.
guestfish -a "${OUTPUT}" -i <"${GF_SCRIPT}"

echo ""
echo "Done! Image created: ${OUTPUT}"
