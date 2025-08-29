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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_proto_rust_lib",
    srcs = glob(["src/**"]),
    deps = [
        "//oak_proto_rust",
        "@oak_crates_index//:p256",
    ],
)

rust_test(
    name = "oak_proto_rust_lib_tests",
    crate = ":oak_proto_rust_lib",
    data = [
        "//oak_proto_rust/oak_proto_rust_lib/testdata:developer_key_public_key",
    ],
    deps = [
        "//oak_file_utils",
        "//oak_proto_rust",
        "@oak_crates_index//:googletest",
        "@oak_crates_index//:p256",
    ],
)
