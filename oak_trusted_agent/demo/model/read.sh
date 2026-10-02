#!/bin/bash
#
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

# Decodes and displays the in-toto Statement and Predicate from a downloaded
# evaluation bundle's signed.json.
#
# Usage:
#   ./oak_trusted_agent/demo/model/read.sh [dir]

set -euo pipefail

readonly OUT_DIR="${1:-/tmp/trusted_eval}"
readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"

cd "${REPO_ROOT}"
bazel run --config=release --ui_event_filters=-info,-stderr --noshow_progress \
  //oak_trusted_agent/provenance/verifier:oak_trusted_agent_provenance_reader -- \
  --statement="${OUT_DIR}/signed.json"
