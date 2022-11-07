#
# Copyright 2022 The Project Oak Authors
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

load(
    "//cc/tflite_micro:build_defs.bzl",
    "oak_copts",
)
load(
    "//cc:build_defs.bzl",
    "cc_static_library",
)

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

cc_library(
    name = "start_file",
    srcs = ["start.S"],
)

cc_library(
    name = "core",
    srcs = ["core.cc"],
    copts = oak_copts(),
    linkstatic = 1,
    deps = [
        "//cc/tflite_micro",
        "//cc/tflite_micro:hdrs",
    ],
)

# Fully static library linked by oak_tensorflow_service.
cc_static_library(
    name = "core_full_static",
    deps = [":core"],
)
