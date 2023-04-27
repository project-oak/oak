#!/bin/bash
#
# A proof-of-concept script to convert a docker image into an initramfs image.
#

# exit when any command fails
set -e

print_usage_and_exit() {
  echo "Usage:"
  echo "  $0 [options] -d <docker-image>

  Exports the filesystem in the Docker image to a directory or an initramfs image.

Options:
    -h                    Display this help and exit.
    -r <rootfs-dir>       Export the Docker filesystem as chroot tree at given directory.
                          If this is not specified, the image will be exported to a newly
                          created temporary directory.
    -o <initramfs-file>   Export the Docker filesystem as the given initramfs file."
  exit 0
}

while getopts "hd:r:o:" opt; do
  case $opt in
    h)
      print_usage_and_exit;;
    o)
      readonly INITRAMFS_FILE="${OPTARG}";;
    r)
      readonly ROOTFS_DIR="${OPTARG}";;
    d)
      readonly DOCKER_IMAGE="${OPTARG}";;
    *)
      echo "Invalid argument: ${OPTARG}"
      exit 1;;
  esac
done

if [ -z "${DOCKER_IMAGE}" ]; then
  echo "Missing required option: -d <docker-image>"
  exit 1
fi

if [ -z "${ROOTFS_DIR}" ]; then
  ROOTFS_DIR=$(mktemp -d)
  echo "[WARN] Directory for the rootfs is not specified. Created ${ROOTFS_DIR}."
fi

echo "[INFO] Rootfs directory is ${ROOTFS_DIR}"
echo "[INFO] Building init process for docker rootfs..."
cargo build --release --target=x86_64-unknown-linux-musl --package=oak_docker_linux_init

# Create a temporary workspace directory.
SCRATCH_DIR=$(mktemp -d)

echo -n "[INFO] Exporting the filesystem in the docker image..."
DOCKER_IMAGE_FS=${SCRATCH_DIR}/filesystem.tar
docker export "$(docker create "${DOCKER_IMAGE}")" \
  -o "${DOCKER_IMAGE_FS}"
echo "done."

# Extract the docker CMD if it is present.
DOCKER_CMD=$(docker \
             inspect \
             --format='{{join .Config.Cmd "\n"}}' \
             "${DOCKER_IMAGE}")

if [ -z "${DOCKER_CMD}" ]; then
  echo "[INFO] 'CMD' not found in docker image. Searching for 'ENTRY_POINT'"
  DOCKER_CMD=$(docker \
               inspect \
               --format='{{join .Config.Entrypoint "\n"}}' \
               "${DOCKER_IMAGE}") 
fi

if [ -z "${DOCKER_CMD}" ]; then
  echo "[ERROR] Neither 'CMD' or 'ENTRYPOINT' found in docker image."
  exit 1
fi

echo "[INFO] Docker entry point cmd: \"${DOCKER_CMD}\""

# Extract the contents of the docker filesystem
tar xf "${DOCKER_IMAGE_FS}" -C "${ROOTFS_DIR}"

# Create a shell script for the docker command.
cat > "${ROOTFS_DIR}/docker_cmd" <<EOF
${DOCKER_CMD}
EOF
chmod a+x "${ROOTFS_DIR}/docker_cmd"

# Create the init file for the initramfs
cp --archive target/x86_64-unknown-linux-musl/release/oak_docker_linux_init \
    "${ROOTFS_DIR}/init"
chmod a+x "${ROOTFS_DIR}/init"

# If /dev/console is present, we are not able to see the output
# from qemu. I presume this is caused by incorrect setup  of character
# devices or terminal. Remove it for now. 
rm -f "${ROOTFS_DIR}/dev/console"

if [ -z "${INITRAMFS_FILE}" ]; then
  echo "[INFO] Leaving docker image as rootfs."
else
  echo "[INFO] Creating initramfs file at ${INITRAMFS_FILE}..."
  ( cd "${ROOTFS_DIR}"; find . -print0 \
      | cpio --null --create --format=newc ) \
      | gzip \
      > "${INITRAMFS_FILE}"
  echo "[INFO] Creating initramfs file at ${INITRAMFS_FILE}...done"
fi
