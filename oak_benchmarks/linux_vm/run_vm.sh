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
# Runs a QEMU VM with the specified image.
# Supports interactive mode (with console) or headless mode (background).
#

set -o errexit
set -o nounset
set -o pipefail

# Default values.
IMAGE=""
MEMORY="1G"
CPUS="2"
INTERACTIVE=false
HEADLESS=false
ENABLE_SNP=false
QEMU_BINARY="qemu-system-x86_64"

usage() {
  cat <<EOF
Usage: $0 --image=<path> [options]

Required:
  --image=PATH         Path to the qcow2 VM image

Optional:
  --memory=SIZE        Memory size (default: 1G)
  --cpus=N             Number of CPUs (default: 2)
  --port=PORT          Forward host PORT to guest PORT (can be repeated)
  --interactive        Attach to VM console (default if no --headless)
  --headless           Run VM in background without console
  --enable-snp         Enable AMD SEV-SNP (requires compatible hardware)
  --qemu=PATH          Path to QEMU binary (default: qemu-system-x86_64)

Examples:
  # Interactive session with console
  $0 --image=/tmp/my-vm.qcow2 --port=5000

  # Run in background with multiple port forwards
  $0 --image=/tmp/my-vm.qcow2 --port=5000 --port=8080 --headless

  # With SEV-SNP enabled
  $0 --image=/tmp/my-vm.qcow2 --port=5000 --enable-snp
EOF
  exit 1
}

# Collect port forwards.
PORTS=()

# Parse arguments.
for arg in "$@"; do
  case ${arg} in
    --image=*)
      IMAGE="${arg#*=}"
      ;;
    --memory=*)
      MEMORY="${arg#*=}"
      ;;
    --cpus=*)
      CPUS="${arg#*=}"
      ;;
    --port=*)
      PORTS+=("${arg#*=}")
      ;;
    --interactive)
      INTERACTIVE=true
      ;;
    --headless)
      HEADLESS=true
      ;;
    --enable-snp)
      ENABLE_SNP=true
      ;;
    --qemu=*)
      QEMU_BINARY="${arg#*=}"
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
if [[ -z ${IMAGE} ]]; then
  echo "Error: --image is required"
  echo ""
  usage
fi

if [[ ! -f ${IMAGE} ]]; then
  echo "Error: Image not found: ${IMAGE}"
  exit 1
fi

# Default to interactive if not headless.
if [[ ${HEADLESS} == false ]]; then
  INTERACTIVE=true
fi

# Check for QEMU.
if ! command -v "${QEMU_BINARY}" &>/dev/null; then
  echo "Error: QEMU not found: ${QEMU_BINARY}"
  echo "Install with: sudo apt install qemu-system-x86"
  exit 1
fi

# Build QEMU arguments.
QEMU_ARGS=(
  "-enable-kvm"
  "-cpu" "host"
  "-m" "${MEMORY}"
  "-smp" "${CPUS}"
  "-drive" "file=${IMAGE},format=qcow2"
  "-net" "nic,model=virtio"
)

# Build network arguments with port forwards.
NET_USER_ARGS="user"
for port in "${PORTS[@]}"; do
  NET_USER_ARGS+=",hostfwd=tcp::${port}-:${port}"
done
QEMU_ARGS+=("-net" "${NET_USER_ARGS}")

# Add SEV-SNP if requested.
if [[ ${ENABLE_SNP} == true ]]; then
  echo "Enabling SEV-SNP..."
  QEMU_ARGS+=(
    "-machine" "q35,confidential-guest-support=sev0,memory-encryption=sev0"
    "-object" "sev-snp-guest,id=sev0,cbitpos=51,reduced-phys-bits=1"
  )
else
  QEMU_ARGS+=("-machine" "q35")
fi

# Console settings.
if [[ ${INTERACTIVE} == true ]]; then
  QEMU_ARGS+=("-nographic")
  echo "Starting VM (interactive mode)..."
  echo "  Image:  ${IMAGE}"
  echo "  Memory: ${MEMORY}"
  echo "  CPUs:   ${CPUS}"
  if [[ ${#PORTS[@]} -gt 0 ]]; then
    echo "  Ports:  ${PORTS[*]}"
  fi
  if [[ ${ENABLE_SNP} == true ]]; then
    echo "  SEV-SNP: enabled"
  fi
  echo ""
  echo "Press Ctrl+A, X to exit the VM."
  echo ""

  exec "${QEMU_BINARY}" "${QEMU_ARGS[@]}"
else
  # Headless mode.
  QEMU_ARGS+=(
    "-nographic"
    "-serial" "none"
    "-monitor" "none"
  )

  echo "Starting VM (headless mode)..."
  echo "  Image:  ${IMAGE}"
  echo "  Memory: ${MEMORY}"
  echo "  CPUs:   ${CPUS}"
  if [[ ${#PORTS[@]} -gt 0 ]]; then
    echo "  Ports:  ${PORTS[*]}"
  fi
  if [[ ${ENABLE_SNP} == true ]]; then
    echo "  SEV-SNP: enabled"
  fi
  echo ""
  echo "Press Ctrl+C to stop the VM."
  echo ""

  exec "${QEMU_BINARY}" "${QEMU_ARGS[@]}"
fi
