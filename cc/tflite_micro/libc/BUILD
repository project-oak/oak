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

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

# Pico libc for TFLM on Oak Restricted Kernel.
cc_library(
    name = "libc",
    srcs = [
        "bsearch.c",
        "ctypes.c",
        "misc.cc",
        "stdlib.c",
    ] + select({
        "//cc/tflite_micro:no_sse": ["string.c"],
        "//conditions:default": glob(["string/*.S"]) + ["string/memset.cc"],
    }),
    hdrs = glob(["**/*.h"]) + [
        "strtox.c",
    ] + select({
        "//cc/tflite_micro:no_sse": [],
        "//conditions:default": glob(["string/*.S"]),
    }),
    copts = ["-Icc/tflite_micro/libc/include"],
)
