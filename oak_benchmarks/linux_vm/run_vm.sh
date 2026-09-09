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
VM_TYPE="default"
QEMU_BINARY="qemu-system-x86_64"
BIOS=""
CBITPOS="51"
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
  --vm-type=TYPE       default (no memory encryption), sev, sev-es or sev-snp
  --qemu=PATH          Path to QEMU binary (default: qemu-system-x86_64)
  --bios=PATH          Firmware blob, needed by a confidential guest
  --cbitpos=N          Encryption bit position (default: 51, Milan and Genoa;
                       Naples and Rome use 47)

Network modes:
  user  QEMU's user-mode (SLIRP) stack, reached through --port forwards. Needs
        no privileges, and is much slower than a real NIC, so it is a
        pessimistic baseline for anything that measures the network.
  tap   A pre-created tap device with the in-kernel vhost datapath. --port is
        ignored; reach the guest on its own address. Setup is in README.md.

VM types:
  The names and the QEMU objects behind them are the ones the Oak launcher
  uses, so the Linux guest and the Restricted Kernel are asked for the same
  thing. Anything other than default needs the host to have SEV enabled and
  /dev/sev to be usable, and needs --bios to point at firmware that supports
  it: the distribution's SeaBIOS does not, and neither does most packaged
  OVMF.

Examples:
  # Interactive session with console
  $0 --image=/tmp/my-vm.qcow2 --port=5000

  # Run in background with multiple port forwards
  $0 --image=/tmp/my-vm.qcow2 --port=5000 --port=8080 --headless

  # Over a real NIC rather than SLIRP
  $0 --image=/tmp/my-vm.qcow2 --net=tap --headless

  # As a confidential guest
  $0 --image=/tmp/my-vm.qcow2 --port=5000 --vm-type=sev-snp \\
      --bios=/usr/share/ovmf/OVMF.fd
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
    --vm-type=*)
      VM_TYPE="${arg#*=}"
      ;;
    --qemu=*)
      QEMU_BINARY="${arg#*=}"
      ;;
    --bios=*)
      BIOS="${arg#*=}"
      ;;
    --cbitpos=*)
      CBITPOS="${arg#*=}"
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

# A memory-encrypted guest cannot drive a virtio device that does not offer
# VIRTIO_F_ACCESS_PLATFORM: Linux refuses to probe one and the guest comes up
# with no NIC at all. QEMU offers that feature when the device has
# iommu_platform=on, which makes the driver route DMA through the bounce
# buffers SEV forces it to use.
#
# https://github.com/torvalds/linux/blob/master/drivers/virtio/virtio.c
# https://github.com/AMDESE/AMDSEV/blob/master/launch-qemu.sh
#
# The plain guest is left without the properties rather than slowed down to
# match: bounce buffers are part of what a confidential guest costs, not a
# difference in how the two were configured.
NIC_PROPS=""
if [[ ${VM_TYPE} != default ]]; then
  NIC_PROPS=",disable-legacy=on,iommu_platform=on"
fi

# Networking. Both modes use the `-netdev` form, since the legacy `-net nic`
# cannot carry device properties; the two forms must not be mixed, because
# together they give the guest two NICs and it configures whichever it sees
# first.
case ${NET} in
  user)
    NET_USER_ARGS="user,id=net0"
    for port in "${PORTS[@]}"; do
      NET_USER_ARGS+=",hostfwd=tcp:127.0.0.1:${port}-:${port}"
    done
    QEMU_ARGS+=(
      "-netdev" "${NET_USER_ARGS}"
      "-device" "virtio-net-pci,netdev=net0${NIC_PROPS}"
    )
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
      "-device" "virtio-net-pci,netdev=net0${NIC_PROPS}"
    )
    ;;
  *)
    echo "Error: unknown --net mode: ${NET} (expected user or tap)"
    exit 1
    ;;
esac

# Confidential guest. The machine stays q35 because this guest boots a
# distribution image rather than a kernel, so oak_launcher_utils' microvm
# arguments do not carry over wholesale.
case ${VM_TYPE} in
  default)
    QEMU_ARGS+=("-machine" "q35")
    ;;
  sev | sev-es | sev-snp)
    if [[ ! -e /dev/sev ]]; then
      echo "Error: --vm-type=${VM_TYPE} needs /dev/sev, which this host does not have"
      echo "Check that the firmware has SEV enabled and that kvm_amd loaded with sev=1"
      exit 1
    fi
    if [[ ! -r /dev/sev ]] || [[ ! -w /dev/sev ]]; then
      echo "Error: /dev/sev is not readable and writable, and QEMU opens it to talk"
      echo "to the PSP, so the guest would fail to launch"
      echo "Grant the kvm group access, then log back in:"
      echo "  echo 'KERNEL==\"sev\", MODE=\"0660\", GROUP=\"kvm\"' |"
      echo "      sudo tee /etc/udev/rules.d/71-sev.rules"
      echo "  sudo udevadm control --reload && sudo udevadm trigger --name-match=sev"
      exit 1
    fi
    if [[ -z ${BIOS} ]]; then
      echo "Error: --vm-type=${VM_TYPE} needs --bios: a confidential guest boots"
      echo "firmware carrying a SEV metadata table, which SeaBIOS does not have"
      exit 1
    fi
    # cbitpos is checked against the host and refused if it disagrees. 51 is
    # right for Milan and Genoa, 47 for Naples and Rome; AMD's reference script
    # reads it from CPUID 0x8000001F EBX[5:0] instead of assuming.
    #
    # reduced-phys-bits is not checked against anything: QEMU only requires 1 to
    # 63, and it reaches the guest as CPUID 0x8000001F EBX[11:6], which Linux
    # subtracts from its physical address width. Hardware that reduces more than
    # this says only leaves the guest believing in address bits it will never
    # place anything at. QEMU's own capabilities query reports 1 regardless.
    SEV_CONFIG="id=sev0,cbitpos=${CBITPOS},reduced-phys-bits=1"
    case ${VM_TYPE} in
      sev) GUEST_OBJECT="sev-guest,${SEV_CONFIG},policy=0x1" ;;
      sev-es) GUEST_OBJECT="sev-guest,${SEV_CONFIG},policy=0x5" ;;
      sev-snp) GUEST_OBJECT="sev-snp-guest,${SEV_CONFIG},id-auth=" ;;
    esac
    QEMU_ARGS+=(
      "-machine" "q35,confidential-guest-support=sev0,memory-backend=ram1"
      "-object" "memory-backend-memfd,id=ram1,size=${MEMORY},share=true,reserve=false"
      "-object" "${GUEST_OBJECT}"
    )
    ;;
  *)
    echo "Error: unknown --vm-type: ${VM_TYPE} (expected default, sev, sev-es or sev-snp)"
    exit 1
    ;;
esac

if [[ -n ${BIOS} ]]; then
  if [[ ! -f ${BIOS} ]]; then
    echo "Error: firmware not found: ${BIOS}"
    exit 1
  fi
  QEMU_ARGS+=("-bios" "${BIOS}")
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
  if [[ ${VM_TYPE} != default ]]; then
    echo "  Type:   ${VM_TYPE}"
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
  if [[ ${VM_TYPE} != default ]]; then
    echo "  Type:   ${VM_TYPE}"
  fi
  echo ""
  echo "Press Ctrl+C to stop the VM."
  echo ""

  exec "${QEMU_BINARY}" "${QEMU_ARGS[@]}"
fi
