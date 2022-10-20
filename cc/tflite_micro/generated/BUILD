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
    "//cc/tflite_micro/oak:build_defs.bzl",
    "oak_copts",
)

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

cc_library(
    name = "tflm",
    hdrs = glob([
        "tensorflow/lite/**/*.h",
        "third_party/flatbuffers/**/*.h",
        "third_party/gemmlowp/**/*.h",
        "third_party/ruy/**/*.h",
    ]),
    srcs = glob(
        ["tensorflow/lite/**/*.cc"],
        exclude = [
            "tensorflow/lite/micro/debug_log.cc",
        ],
    ),
    copts = oak_copts(),
    deps = [
        # Use Oak DebugLog implementation
        "//cc/tflite_micro/oak:debug_log",
        # Use Oak minimal stdlib
        "//cc/tflite_micro/oak/stdlib",
    ],
    linkstatic = 1,
)
