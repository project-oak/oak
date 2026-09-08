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
NET="user"
TAP_DEVICE="oaktap0"

usage() {
  cat <<EOF
Usage: $0 --image=<path> [options]

Required:
  --image=PATH         Path to the qcow2 VM image

Optional:
  --memory=SIZE        Memory size (default: 1G)
  --cpus=N             Number of CPUs (default: 2)
  --port=PORT          Forward host PORT to guest PORT (user networking only,
                       can be repeated)
  --net=MODE           user (default) or tap. See below.
  --tap-device=NAME    Tap device for --net=tap (default: oaktap0)
  --interactive        Attach to VM console (default if no --headless)
  --headless           Run VM in background without console
  --enable-snp         Enable AMD SEV-SNP (requires compatible hardware)
  --qemu=PATH          Path to QEMU binary (default: qemu-system-x86_64)

Network modes:
  user  QEMU's user-mode (SLIRP) stack, reached through --port forwards. Needs
        no privileges, and is much slower than a real NIC, so it is a
        pessimistic baseline for anything that measures the network.
  tap   A pre-created tap device with the in-kernel vhost datapath. --port is
        ignored; reach the guest on its own address. Setup is in README.md.

Examples:
  # Interactive session with console
  $0 --image=/tmp/my-vm.qcow2 --port=5000

  # Run in background with multiple port forwards
  $0 --image=/tmp/my-vm.qcow2 --port=5000 --port=8080 --headless

  # Over a real NIC rather than SLIRP
  $0 --image=/tmp/my-vm.qcow2 --net=tap --headless

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
    --net=*)
      NET="${arg#*=}"
      ;;
    --tap-device=*)
      TAP_DEVICE="${arg#*=}"
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
  "-drive" "file=${IMAGE},format=qcow2,snapshot=on"
)

# Networking. The legacy `-net nic` form and the `-netdev` form cannot be mixed:
# together they give the guest two NICs, and the guest configures whichever it
# sees first.
case ${NET} in
  user)
    NET_USER_ARGS="user"
    for port in "${PORTS[@]}"; do
      NET_USER_ARGS+=",hostfwd=tcp:127.0.0.1:${port}-:${port}"
    done
    QEMU_ARGS+=("-net" "nic,model=virtio" "-net" "${NET_USER_ARGS}")
    ;;
  tap)
    if [[ ! -d /sys/class/net/${TAP_DEVICE} ]]; then
      echo "Error: tap device not found: ${TAP_DEVICE}"
      echo "Create it once, as root:"
      echo "  sudo ip tuntap add dev ${TAP_DEVICE} mode tap user \${USER}"
      echo "  sudo ip addr add 198.18.0.1/30 dev ${TAP_DEVICE}"
      echo "  sudo ip link set ${TAP_DEVICE} up"
      exit 1
    fi
    if [[ ! -w /dev/vhost-net ]]; then
      echo "Error: /dev/vhost-net is not writable, so this mode would measure"
      echo "QEMU's userspace NIC emulation instead of the kernel datapath."
      echo "Grant access once, as root:"
      echo "  sudo setfacl -m u:\${USER}:rw /dev/vhost-net"
      exit 1
    fi
    if [[ ${#PORTS[@]} -gt 0 ]]; then
      echo "Note: --port is ignored with --net=tap; the guest has its own address."
    fi
    QEMU_ARGS+=(
      "-netdev" "tap,id=net0,ifname=${TAP_DEVICE},script=no,downscript=no,vhost=on"
      "-device" "virtio-net-pci,netdev=net0"
    )
    ;;
  *)
    echo "Error: unknown --net mode: ${NET} (expected user or tap)"
    exit 1
    ;;
esac

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
  if [[ ${NET} == tap ]]; then
    echo "  Net:    tap ${TAP_DEVICE}, vhost=on"
  else
    echo "  Net:    user-mode (SLIRP)"
  fi
  if [[ ${#PORTS[@]} -gt 0 ]] && [[ ${NET} == user ]]; then
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
  if [[ ${NET} == tap ]]; then
    echo "  Net:    tap ${TAP_DEVICE}, vhost=on"
  else
    echo "  Net:    user-mode (SLIRP)"
  fi
  if [[ ${#PORTS[@]} -gt 0 ]] && [[ ${NET} == user ]]; then
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
