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

docker build . --tag=oak-containers-sysimage-base:latest --file base_image.Dockerfile

readonly DOCKER_IMAGE_NAME='europe-west2-docker.pkg.dev/oak-ci/oak-containers-sysimage-base/oak-containers-sysimage-base:latest'
docker tag oak-containers-sysimage-base:latest "${DOCKER_IMAGE_NAME}"
docker push "${DOCKER_IMAGE_NAME}"
