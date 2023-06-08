#!/bin/bash
#
# Extract a Linux kernel and prepares an initramfs directory by
# combining the following:
#    - Alpine Linux's minirootfs.
#    - Necessary drivers copied from an Alpine Linux distribution.
#    - Filesystem extracted from the given docker image.
#

# exit when any command fails.
set -e

readonly SCRIPT_DIR=$(dirname "$0")

print_usage_and_exit() {
  echo "Usage:
  ${0} [-h] \\
       -k <output-linux-kernel> \\
       -o <output-initramfs>    \\
       -q <qcow2-file>          \\
       -d <docker-image>

Creates an initramfs with minirootfs+networking support as docker launcher.

Options:
  -k      Location for the extracted Linux kernel.
  -d      Docker image that should be launched.
  -q      Extract docker image as a qcow2 image instead of packing in initramfs.
  -o      Output initramfs file.
  -h      Print this help message and exit."
  exit 0
}

while getopts "hk:d:o:q:" opt; do
  case $opt in
    h)
      print_usage_and_exit;;
    k)
      readonly LINUX_KERNEL="${OPTARG}";;
    d)
      readonly DOCKER_IMAGE="${OPTARG}";;
    o)
      readonly OUTPUT_INITRAMFS="${OPTARG}";;
    q)
      readonly DOCKER_QCOW2_IMAGE="${OPTARG}";;
    *)
      echo "Invalid argument: ${OPTARG}"
      exit 1;;
  esac
done

if [ -z "${LINUX_KERNEL}" ]; then
  echo "Missing required option: -k <output-linux-kernel>"
  exit 1
fi

if [ -z "${OUTPUT_INITRAMFS}" ]; then
  echo "Missing required option: -o <output-initramfs>"
  exit 1
fi

# Create a temporary workspace directory.
readonly SCRATCH_DIR=$(mktemp -d)
echo "[INFO] Scratch directory is ${SCRATCH_DIR}"
# Make a directory for the initramfs.
readonly RAMDIR=$(mktemp -d)
echo "[INFO] Ramdisk staging directory is ${RAMDIR}"
echo "[INFO] Preparing ${RAMDIR} with a minimal rootfs and drivers."
echo "[INFO] Preparing docker image for extraction..."
docker build -t mkinitramfs "${SCRIPT_DIR}"
echo "[INFO] Extracting a minimal rootfs and drivers..."
docker run -v "${RAMDIR}:/output" -it mkinitramfs \
  sh -c "/app/mk_base_initramfs.sh -k /output/vmlinux -r /output"

echo "[INFO] Updating Linux kernel at ${LINUX_KERNEL}"
mkdir -p "$(dirname "${LINUX_KERNEL}")"
mv "${RAMDIR}/vmlinux" "${LINUX_KERNEL}"

if [ -z "${DOCKER_IMAGE}" ]; then
  echo "[WARN] No docker image specified. initramfs will launch a shell."
  echo "       Use -d option to specify docker image if needed."
  readonly LAUNCH_CMD="exec /sbin/getty -n -l /bin/sh 115200 /dev/console"
else
  echo "[INFO] Preparing docker image as a rootfs."
  if [ -z "${DOCKER_QCOW2_IMAGE}" ]; then
    readonly DOCKER_ROOTFS_DIR="${RAMDIR}/docker_rootfs"
  else
    readonly DOCKER_ROOTFS_DIR="${SCRATCH_DIR}/docker_rootfs"
  fi
  mkdir -p "${DOCKER_ROOTFS_DIR}"
  sh "${SCRIPT_DIR}/docker_to_rootfs.sh" \
    -d "${DOCKER_IMAGE}" -r "${DOCKER_ROOTFS_DIR}"
  if [ -z "${DOCKER_QCOW2_IMAGE}" ]; then
    echo "[INFO] Embedding Docker filesystem into initramfs."
  else
    echo "[INFO] Creating QEMU qcow2 image at ${DOCKER_QCOW2_IMAGE}"
    virt-make-fs --format=qcow2 --size=+200M \
      "${DOCKER_ROOTFS_DIR}" "${DOCKER_QCOW2_IMAGE}"
    MOUNT_DOCKER_ROOTFS_CMD="
    # Assumes that the virtual block drive is at /dev/vda.
    mkdir /docker_rootfs
    mount /dev/vda /docker_rootfs
"
  fi
  readonly LAUNCH_CMD="
# copy the resolv.conf file to the chroot.
cp -f /etc/resolv.conf /docker_rootfs/etc/resolv.conf
exec /usr/sbin/chroot /docker_rootfs /init
"
fi

# Create the /init file in the initramfs file.
echo "[INFO] Appending necessary commands to end of /init file"
echo "${MOUNT_DOCKER_ROOTFS_CMD}" >> "${RAMDIR}/init"
echo "${LAUNCH_CMD}" >> "${RAMDIR}/init"
chmod a+x "${RAMDIR}/init"

echo "[INFO] Creating initramfs file at ${OUTPUT_INITRAMFS}..."
(cd "${RAMDIR}"; find . -print0 \
    | cpio --null --create --format=newc ) \
    | gzip > "${OUTPUT_INITRAMFS}"
echo "[INFO] Creating initramfs file at ${OUTPUT_INITRAMFS}...done"
