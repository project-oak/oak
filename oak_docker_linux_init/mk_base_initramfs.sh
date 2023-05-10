#!/bin/bash
#
# Prepares an initramfs file by combining the following:
#    - Alpine Linux's minirootfs.
#    - Necessary drivers copied from an Alpine Linux distribution.
#    - /init script that sets up drivers.

# exit when any command fails.
set -e

readonly DEFAULT_MINIROOTFS_TAR="/app/alpine-minirootfs.tar.gz"

print_usage_and_exit() {
  echo "Usage:
  ${0} [-h] \\
       [-m <alpine-minirootfs>] \\
       -k <output-linux-kernel> \\
       -r <output-initramfs-dir>

Prepares the given directory with a minimal root filesystem along with
the necessary drivers.

Options:
  -k      Location for the extracted linux kernel.
  -r      The output directory for the files in initramfs.
  -m      Alpine's minirootfs tarball. If unspecified, we will use a
          a tar that is packaged with the Alpine Docker image used
          to run this script. (${DEFAULT_MINIROOTFS_TAR})
  -h      Print this help message and exit."
  exit 0
}

while getopts "hm:r:k:" opt; do
  case $opt in
    h)
      print_usage_and_exit;;
    k)
      readonly LINUX_KERNEL="${OPTARG}";;
    m)
      readonly ALPINE_MINIROOTFS_TAR="${OPTARG}";;
    r)
      readonly RAMDIR="${OPTARG}";;
    *)
      echo "Invalid argument: ${OPTARG}"
      exit 1;;
  esac
done

if [ -z "${LINUX_KERNEL}" ]; then
  echo "Missing required option: -k <output-linux-kernel>"
  exit 1
fi

if [ -z "${RAMDIR}" ]; then
  echo "Missing required option: -r <output-initramfs-dir>"
  exit 1
fi

if [ -z "${ALPINE_MINIROOTFS_TAR}" ]; then
  echo "Missing option: -m <alpine-minirootfs>."
  echo "Using ${DEFAULT_MINIROOTFS_TAR} as the minirootfs tar."
  ALPINE_MINIROOTFS_TAR="${DEFAULT_MINIROOTFS_TAR}"
fi

# Make a directory for the initramfs.
echo "[INFO] Ramdisk staging directory is ${RAMDIR}"

# Extract the uncompressed linux kernel.
echo "[INFO] Extracting the uncompressed linux kernel to ${LINUX_KERNEL}"
EXTRACT_VMLINUX="$(find /usr/src -name 'extract-vmlinux')"
sh "${EXTRACT_VMLINUX}" /boot/vmlinuz-virt > "${LINUX_KERNEL}"

# Extract the linux version string from the kernel image.
readonly LINUX_KERNEL_VERSION="$(strings "${LINUX_KERNEL}" | \
                                 grep "Linux version" | cut -d\  -f3)"
echo "[INFO] Linux kernel version is ${LINUX_KERNEL_VERSION}"

# Extract the minirootfs to the root of the ramdisk.
echo "[INFO] Extracting ${ALPINE_MINIROOTFS_TAR} to ${RAMDIR}"
tar xzf "${ALPINE_MINIROOTFS_TAR}" -C "${RAMDIR}"

# Extract the drivers from the initramfs and put them in ${RAMDIR}.
echo "[INFO] Extracting necessary drivers."
readonly NETWORK_DRIVERS="
kernel/drivers/net/virtio_net.ko.gz
kernel/drivers/net/net_failover.ko.gz
kernel/net/core/failover.ko.gz
kernel/net/packet/af_packet.ko.gz
"
readonly IPV6_DRIVERS="
kernel/net/ipv6/ipv6.ko.gz
"
readonly BLOCK_DEVICE_DRIVERS="
kernel/drivers/block/virtio_blk.ko.gz
"
readonly EXT4_DRIVERS="
kernel/fs/ext4/ext4.ko.gz
kernel/lib/crc16.ko.gz
kernel/fs/mbcache.ko.gz
kernel/fs/jbd2/jbd2.ko.gz
kernel/crypto/crc32c_generic.ko.gz
"
readonly DRIVERS="
${NETWORK_DRIVERS}
${IPV6_DRIVERS}
${BLOCK_DEVICE_DRIVERS}
${EXT4_DRIVERS}
"

# Copy relevant modules to ${RAMDIR}
readonly MODULES_DEP="/lib/modules/${LINUX_KERNEL_VERSION}/modules.dep"
for DRIVER in ${DRIVERS}; do
  DRIVER_PATH="/lib/modules/${LINUX_KERNEL_VERSION}/${DRIVER}"
  DRIVER_DIR=$(dirname "${DRIVER_PATH}")
  echo "[INFO] Extracting ${DRIVER}"
  mkdir -p "${RAMDIR}/${DRIVER_DIR}" &&
    cp "${DRIVER_PATH}" "${RAMDIR}/${DRIVER_PATH}"
  # Extract the module depedency info.
  grep "^$DRIVER:" "${MODULES_DEP}" >> "${RAMDIR}/${MODULES_DEP}"
done

# Create the /init file in the initramfs file.
echo "[INFO] Preparing /init file for initramfs"
cat > "${RAMDIR}/init" <<EOF
#!/bin/sh
#
# /init executable file in the initramfs
#
mount -t devtmpfs dev /dev
mount -t proc proc /proc
mount -t sysfs sysfs /sys

# Load drivers
modprobe virtio_net
modprobe af_packet
modprobe ipv6
modprobe virtio_blk
modprobe crc32c_generic
modprobe ext4

# Bring up network interfaces.
ip link set up dev lo
ip link set eth0 up
udhcpc -i eth0

EOF
chmod a+x "${RAMDIR}/init"
