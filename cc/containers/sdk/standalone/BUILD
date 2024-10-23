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

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

cc_library(
    name = "oak_standalone",
    srcs = ["oak_standalone.cc"],
    hdrs = ["oak_standalone.h"],
    deps = [
        "//oak_containers_sdk:ffi",
        "//proto/session:messages_cc_proto",
        "@com_google_absl//absl/log",
        "@com_google_absl//absl/status:statusor",
    ],
)

cc_test(
    name = "oak_standalone_test",
    srcs = ["oak_standalone_test.cc"],
    deps = [
        ":oak_standalone",
        "//oak_containers_sdk:ffi",
        "//proto/session:messages_cc_proto",
        "@com_google_absl//absl/log",
        "@com_google_absl//absl/status:statusor",
        "@com_google_googletest//:gtest_main",
    ],
)
