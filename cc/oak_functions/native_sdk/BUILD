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

load("//cc/oak_functions/native_sdk:native_rules.bzl", "oak_functions_native_module")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

cc_library(
    name = "native_sdk",
    srcs = [
        "native_sdk.cc",
        "native_sdk_ffi.h",
    ],
    hdrs = ["native_sdk.h"],
    deps = [
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

oak_functions_native_module(
    name = "key_value_lookup",
    srcs = ["key_value_lookup.cc"],
    deps = [
        "@com_google_absl//absl/log:check",
    ],
)
