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
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

cc_library(
    name = "cxx_string_test_foreign",
    srcs = ["cxx_string_test_foreign.cc"],
    hdrs = ["cxx_string_test_foreign.h"],
    deps = [
        "//cc/ffi:bytes_bindings",
        "//cc/ffi:bytes_view",
        "//cc/ffi:cxx_string",
        "@com_google_absl//absl/strings",
    ],
)

rust_library(
    name = "oak_ffi_bytes",
    srcs = ["bytes.rs"],
)

rust_library(
    name = "oak_ffi_error",
    srcs = ["error.rs"],
    deps = [":oak_ffi_bytes"],
)

rust_library(
    name = "cxx_string",
    srcs = ["cxx_string.rs"],
    deps = [
        "//cc/ffi:cxx_string",
    ],
)

rust_test(
    name = "cxx_string_test",
    crate = ":cxx_string",
    deps = [
        ":cxx_string_test_foreign",
        ":oak_ffi_bytes",
        "//cc/ffi:cxx_string",
    ],
)

rust_library(
    name = "absl_status",
    srcs = ["absl_status.rs"],
    deps = [
        ":oak_ffi_bytes",
        "//cc/ffi:absl_status",
    ],
)

cc_library(
    name = "absl_status_test_foreign",
    srcs = ["absl_status_test_foreign.cc"],
    deps = [
        "//cc/ffi:absl_status",
        "//cc/ffi:bytes_view",
        "@com_google_absl//absl/log:die_if_null",
        "@com_google_absl//absl/status",
    ],
)

rust_test(
    name = "absl_status_test",
    crate = ":absl_status",
    deps = [
        ":absl_status_test_foreign",
        ":oak_ffi_bytes",
    ],
)
