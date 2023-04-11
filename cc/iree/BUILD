#
# Copyright 2023 The Project Oak Authors
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

load("//cc:build_defs.bzl", "cc_static_library")

package(
    licenses = ["notice"],
)

cc_library(
    name = "iree_wrapper",
    srcs = [
        # To link with an internally compiled IREE model - replace `iree.cc` with `libiree_core.a`.
        "iree.cc",
        # "libiree_core.a",
    ],
    hdrs = ["iree.h"],
    features = ["fully_static_link"],
    linkstatic = 1,
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "//:os_oak",
    ],
)

# Fully static library linked by an Oak enclave application.
cc_static_library(
    name = "iree",
    deps = [":iree_wrapper"],
)
