#!/bin/bash

set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

readonly SCRIPTS_DIR="$(dirname "$0")"

cd "$SCRIPTS_DIR"

# Fix the file permissions that will be loaded into the system image, as Git doesn't track them.
# Unfortunately we can't do it in Dockerfile (with `COPY --chown`), as that requires BuildKit.
chmod --recursive a+rX files/

readonly OCI_IMAGE_FILE="./target/oak_container_sysimage_oci_image_base.tar"
readonly OCI_BUNDLE_FILE="./target/oak_container_sysimage_oci_image_base_bundle.tar"

# Export the container as an OCI Image.
# Ref: https://docs.docker.com/build/exporters/oci-docker/
readonly BUILDER="$(docker buildx create --driver docker-container)"
docker buildx \
    --builder="${BUILDER}" \
    build \
    --tag="latest" \
    --output="type=oci,dest=${OCI_IMAGE_FILE}" \
    --file base_image.Dockerfile \
    .

../scripts/export_container_bundle \
    -c "${OCI_IMAGE_FILE}" \
    -o "${OCI_BUNDLE_FILE}"

#bazel run push_base
