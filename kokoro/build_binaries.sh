#!/usr/bin/env bash

# NOTE: This is WIP. For now it only builds a single binary. Once we are
# certain this approach works, we will update it to build all binaries.

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

export CI=kokoro

export RUST_BACKTRACE=1
export RUST_LOG=debug
export XDG_RUNTIME_DIR=/var/run

readonly ROOT_DIR="$(dirname "$0" | cut -d/ -f1)"
# shellcheck source=scripts/common
source "$ROOT_DIR/scripts/common"

# Download the builder tool
curl --location https://github.com/slsa-framework/slsa-github-generator/releases/download/v1.7.0/slsa-builder-docker-linux-amd64 --output builder
chmod +x builder

# Build the binary. Should be made parametric.
./builder build \
 --build-config-path buildconfigs/oak_restricted_kernel_simple_io_bin.toml \
 --builder-image "$DOCKER_IMAGE_REPO_DIGEST" \
 --git-commit-digest "sha1:$KOKORO_GITHUB_COMMIT" \
 --source-repo git+https://github.com/project-oak/oak@refs/heads/main \
 --subjects-path subjects.json \
 --output-folder "/tmp/build-outputs-$KOKORO_GITHUB_COMMIT" \
 --verbose

# Copy the generated binary to placer
cp /tmp/build-outputs/oak_restricted_kernel_simple_io_bin "$KOKORO_ARTIFACTS_DIR/latest/oak_restricted_kernel_simple_io_bin/$KOKORO_GITHUB_COMMIT"
ls -als "$KOKORO_ARTIFACTS_DIR"
