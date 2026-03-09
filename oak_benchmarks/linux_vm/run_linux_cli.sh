#!/bin/bash
# Copyright 2026 The Project Oak Authors
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

set -e

# The script executes in the runfiles tree, so expanding with $PWD gives absolute paths.
CLI="${PWD}/$1"
IMAGE="${PWD}/$2"
RUN_VM_SCRIPT="${PWD}/$3"
shift 3

# Pass absolute paths so linux_cli doesn't attempt to resolve them relative to BUILD_WORKSPACE_DIRECTORY
exec "${CLI}" \
  --vm-image="${IMAGE}" \
  --run-vm-script="${RUN_VM_SCRIPT}" "$@"
