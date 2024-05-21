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

constraint_value(
    name = "os_oak",
    constraint_setting = "@platforms//os:os",
)

platform(
    name = "oak",
    constraint_values = [
        "//:os_oak",
        "@platforms//cpu:x86_64",
    ],
)

platform(
    name = "x86_64-unknown-none",
    constraint_values = [
        "@platforms//cpu:x86_64",
        "@platforms//os:none",
    ],
)

filegroup(
    name = "clang_tidy_config",
    srcs = [".clang-tidy"],
    visibility =
        ["//visibility:public"],
)
