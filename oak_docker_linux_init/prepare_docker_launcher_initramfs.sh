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
echo "[INFO] Preparing ${RAMDIR} with a minimal rootfs and drivers."
echo "[INFO] Preparing docker image for extraction..."
docker build -t mkinitramfs "${SCRIPT_DIR}"
echo "[INFO] Extracting a minimal rootfs and drivers..."
docker run -v "${RAMDIR}:/output" -it mkinitramfs \
  sh -c "/app/mk_base_initramfs.sh -k /output/vmlinux -r /output"

echo "[INFO] Updating Linux kernel at ${LINUX_KERNEL}"
mv "${RAMDIR}/vmlinux" "${LINUX_KERNEL}"

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
