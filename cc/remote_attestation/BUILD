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

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

cc_library(
    name = "attestation_verifier",
    hdrs = ["attestation_verifier.h"],
    deps = [
        "//proto/session:messages_cc_proto",
        "@com_google_absl//absl/status",
    ],
)

cc_library(
    name = "insecure_attestation_verifier",
    srcs = ["insecure_attestation_verifier.cc"],
    hdrs = ["insecure_attestation_verifier.h"],
    deps = [
        ":attestation_verifier",
        "//proto/session:messages_cc_proto",
        "@com_google_absl//absl/status",
    ],
)
