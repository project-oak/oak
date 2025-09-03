#!/bin/bash
#
# Copyright 2025 The Project Oak Authors
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

set -o errexit
set -o pipefail
set -o nounset
set -o xtrace
shopt -s inherit_errexit

# Build the input attestation & reference values (binary protobuf) files.
bazel build oak_attestation_verification_cli/examples/certificate_based:attestation_verification_report_input_files

# Run the verification CLI on the generated files.
bazel run //oak_attestation_verification_cli:oak_attestation_verification_cli -- \
    --attestation bazel-bin/oak_attestation_verification_cli/examples/certificate_based/collected_attestation.binpb \
    --reference-values bazel-bin/oak_attestation_verification_cli/examples/certificate_based/reference_values.binpb
