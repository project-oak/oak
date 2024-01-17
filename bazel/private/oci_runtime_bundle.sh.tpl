#!/usr/bin/env bash
#
# Copyright 2024 The Project Oak Authors
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

set -eu

readonly UMOCI="{{umoci}}"
readonly YQ="{{yq}}"

# Add tags to the image index generated by oci_image so that it's compatible
# with umoci.
readonly IMAGE_DIR=$(mktemp -d)
cp -RL "$1/." "${IMAGE_DIR}"
"${YQ}" -i -o=json '.manifests[0].annotations["org.opencontainers.image.ref.name"] = "latest"' "${IMAGE_DIR}/index.json"

# Use umoci to unpack the image into a runtime bundle.
readonly BUNDLE_DIR=$(mktemp -d)
"${UMOCI}" unpack --rootless --image "${IMAGE_DIR}" "${BUNDLE_DIR}"

# Sort mount options, which umoci emits in a non-deterministic order.
"${YQ}" -i -o=json 'with(.mounts ; .[] | select(.options != null) | .options |= sort)' "${BUNDLE_DIR}/config.json"

# Pack the runtime bundle into a (reproducible) tar, excluding unnecessary files
# added by umoci.
tar --create --sort=name --mtime="2000-01-01" --owner=0 --group=0 --numeric-owner \
    --file="$2" --directory="${BUNDLE_DIR}" --exclude=./umoci.json --exclude='./sha256_*.mtree' .
