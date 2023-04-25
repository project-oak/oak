#!/bin/bash
#
# Prepares an initramfs file by combining the following:
#    - Alpine Linux's minirootfs.
#    - Necessary drivers copied from an Alpine Linux distribution.
#    - Filesystem extracted from the given docker image.
#
#

 # exit when any command fails.
set -e

readonly SCRIPT_DIR=$(dirname "$0")

print_usage_and_exit() {
  echo "Usage:
  ${0} [-h] \\
       -k <uncompressed-kernel> \\
       -i <alpine-initiramfs>   \\
       -m <alpine-minirootfs>   \\
       -o <output-initramfs>    \\
       -d <docker-image>

Creates an initramfs with minirootfs+networking support as docker launcher.

Options:
  -k      Uncompressed kernel with which we use the drivers.
  -i      Initramfs extracted from an Alpine iso distribution.
  -m      Alpine's minirootfs tarball.
  -d      Docker image that should be launched.
  -o      Output initramfs file.
  -h      Print this help message and exit."
  exit 0
}

while getopts "hk:i:m:d:o:" opt; do
  case $opt in
    h)
      print_usage_and_exit;;
    k)
      readonly LINUX_KERNEL="${OPTARG}";;
    i)
      readonly ALPINE_INITRAMFS="${OPTARG}";;
    m)
      readonly ALPINE_MINIROOTFS_TAR="${OPTARG}";;
    d)
      readonly DOCKER_IMAGE="${OPTARG}";;
    o)
      readonly OUTPUT_INITRAMFS="${OPTARG}";;
    *)
      echo "Invalid argument: ${OPTARG}"
      exit 1;;
  esac
done

if [ -z "${LINUX_KERNEL}" ]; then
  echo "Missing required option: -k <uncompressed-kernel>"
  exit 1
fi

if [ -z "${ALPINE_INITRAMFS}" ]; then
  echo "Missing required option: -i <alpine-initramfs>"
  exit 1
fi

if [ -z "${OUTPUT_INITRAMFS}" ]; then
  echo "Missing required option: -o <output-initramfs>"
  exit 1
fi

if [ -z "${ALPINE_MINIROOTFS_TAR}" ]; then
  echo "Missing required option: -m <alpine-minirootfs>"
  exit 1
fi

# Create a temporary workspace directory.
readonly SCRATCH_DIR=$(mktemp -d)
echo "[INFO] Scratch directory is ${SCRATCH_DIR}"
# Make a directory for the initramfs.
readonly RAMDIR=$(mktemp -d)
echo "[INFO] Ramdisk staging directory is ${RAMDIR}"

# Extract the linux version string from the kernel image.
readonly LINUX_KERNEL_VERSION="$(strings "${LINUX_KERNEL}" | \
                                 grep "Linux version" | cut -d\  -f3)"
echo "[INFO] Linux kernel version is ${LINUX_KERNEL_VERSION}"


# Extract Alpine's initramfs to a scratch directory.
ALPINE_INITRAMFS_DIR="${SCRATCH_DIR}/alpine-initramfs"
echo "[INFO] Extracting  ${ALPINE_INITRAMFS} to ${ALPINE_INITRAMFS_DIR}"
mkdir "${ALPINE_INITRAMFS_DIR}"
# () is necessary to avoid changing pwd to ${ALPINE_INITRAMFS_DIR}
(cd "${ALPINE_INITRAMFS_DIR}" && \
  gzip -cd "${ALPINE_INITRAMFS}" | cpio -idm)

# Extract the minirootfs to the root of the ramdisk.
tar xzf "${ALPINE_MINIROOTFS_TAR}" -C "${RAMDIR}"

# Extract the drivers from the initramfs and put them in ${RAMDIR}.
echo "[INFO] Extracting necessary drivers from ${ALPINE_INITRAMFS}"
readonly DRIVERS="
kernel/drivers/net/virtio_net.ko
kernel/drivers/net/net_failover.ko
kernel/net/core/failover.ko
kernel/net/packet/af_packet.ko
"

readonly MODULES_DEP="lib/modules/${LINUX_KERNEL_VERSION}/modules.dep"
for DRIVER in ${DRIVERS}; do
  DRIVER_PATH="lib/modules/${LINUX_KERNEL_VERSION}/${DRIVER}"
  DRIVER_DIR=$(dirname "${DRIVER_PATH}")
  echo "[INFO] Extracting ${DRIVER}"
  mkdir -p "${RAMDIR}/${DRIVER_DIR}" &&
    cp "${ALPINE_INITRAMFS_DIR}/${DRIVER_PATH}" "${RAMDIR}/${DRIVER_PATH}"
  # Extract the module depedency info.
  grep "^$DRIVER:" "${ALPINE_INITRAMFS_DIR}/${MODULES_DEP}" \
    >> "${RAMDIR}/${MODULES_DEP}"
done

if [ -z "${DOCKER_IMAGE}" ]; then
  echo "[WARN] No docker image specified. initramfs will launch a shell."
  echo "       Use -d option to specify docker image if needed."
  LAUNCH_CMD="exec /sbin/getty -n -l /bin/sh 115200 /dev/console"
else
  echo "[INFO] Preparing docker image as a rootfs."
  readonly DOCKER_ROOTFS_DIR="${RAMDIR}/docker_rootfs"
  mkdir -p "${DOCKER_ROOTFS_DIR}"
  sh "$SCRIPT_DIR/docker_to_rootfs.sh" \
    -d "${DOCKER_IMAGE}" -r "${DOCKER_ROOTFS_DIR}"
  LAUNCH_CMD="
# copy the resolv.conf file to the chroot.
cp -f /etc/resolv.conf /docker_rootfs/etc/resolv.conf
exec /usr/sbin/chroot /docker_rootfs /init"
fi

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
modprobe virtio-net
modprobe af_packet

# Bring up network interfaces.
ip link set up dev lo
ip link set eth0 up
udhcpc -i eth0

# Launch terminal or docker as needed.
${LAUNCH_CMD}
EOF
chmod a+x "${RAMDIR}/init"

echo "[INFO] Creating initramfs file at ${OUTPUT_INITRAMFS}..."
(cd "${RAMDIR}"; find . -print0 \
    | cpio --null --create --format=newc ) \
    | gzip > "${OUTPUT_INITRAMFS}"
echo "[INFO] Creating initramfs file at ${OUTPUT_INITRAMFS}...done"
