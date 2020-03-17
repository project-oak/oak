#
# Copyright 2019 The Project Oak Authors
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

# An empty BUILD file in the project root is required for `bazel-gazelle` that is
# loaded by `rules_docker`:
# https://github.com/bazelbuild/bazel-gazelle/issues/609

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

# Export LICENSE file for projects that reference Oak in Bazel as an external dependency.
exports_files(["LICENSE"])

# These files are built via cargo outside of Bazel.
exports_files(srcs = glob(["target/wasm32-unknown-unknown/release/*.wasm"]))

# These files are necessary for the backend server in the Aggregator example application.
exports_files(srcs = glob(["target/release/aggregator_*"]))
