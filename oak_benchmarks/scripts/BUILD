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

load("@rules_python//python:defs.bzl", "py_library", "py_test")

package(
    default_visibility = ["//visibility:private"],
    licenses = ["notice"],
)

# These are host-side helper scripts. No Python toolchain is registered for the
# bare-metal target platform, so without an explicit constraint a wildcard build
# such as `just clippy` fails to analyse them rather than skipping them.
py_library(
    name = "check_matrix",
    srcs = ["check_matrix.py"],
    imports = ["."],
    target_compatible_with = ["@platforms//os:linux"],
)

py_test(
    name = "check_matrix_test",
    size = "small",
    srcs = ["check_matrix_test.py"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [":check_matrix"],
)

py_library(
    name = "boot_latency",
    srcs = ["boot_latency.py"],
    imports = ["."],
    target_compatible_with = ["@platforms//os:linux"],
)

py_test(
    name = "boot_latency_test",
    size = "small",
    srcs = ["boot_latency_test.py"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [":boot_latency"],
)
