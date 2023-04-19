#!/bin/bash
#
# A proof-of-concept script to convert a docker image into an initramfs image.
#

# exit when any command fails
set -e

# Just a simple commandline handling for now.
if [ $# -ne 2 ]; then
  echo "Usage:"
  echo "  $0 <docker-image> <output-initramfs-file> "
  exit 1
fi
DOCKER_IMAGE=$1
INITRAMFS_FILE=$2

echo "[Info] Building init process..."
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

# Create initramfs 
RAMDIR=$(mktemp -d)

# Extract the contents of the docker filesystem
tar xf "${DOCKER_IMAGE_FS}" -C "${RAMDIR}"

# Create a shell script for the docker command.
cat > "${RAMDIR}/docker_cmd" <<EOF
${DOCKER_CMD}
EOF
chmod a+x "${RAMDIR}/docker_cmd"

# Create the init file for the initramfs
cp --archive target/x86_64-unknown-linux-musl/release/oak_docker_linux_init \
    "${RAMDIR}/init"
chmod a+x "${RAMDIR}/init"

# If /dev/console is present, we are not able to see the output
# from qemu. I presume this is caused by incorrect setup  of character
# devices or terminal. Remove it for now. 
rm -f "${RAMDIR}/dev/console"

echo "[INFO] Creating initramfs file at ${INITRAMFS_FILE}..."
( cd "${RAMDIR}"; find . -print0 \
    | cpio --null --create --format=newc ) \
    | gzip \
    > "${INITRAMFS_FILE}"
echo "[INFO] Creating initramfs file at ${INITRAMFS_FILE}...done"

