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

# Upstream prost-types depends on prost-derive unconditionally, which means
# we can't use it in our oak_no_std_crates_index.

load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//visibility:public"],
)

rust_library(
    name = "prost-types",
    srcs = glob(["src/**"]),
    proc_macro_deps = [
        "@oak_crates_index//:prost-derive",
    ],
    deps = select({
        "@platforms//os:none": [
            "@oak_no_std_crates_index//:prost",
        ],
        "//conditions:default": [
            "@oak_crates_index//:prost",
        ],
    }),
)
