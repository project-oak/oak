#
# Copyright 2025 The Project Oak Authors
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

load("@rules_shell//shell:sh_test.bzl", "sh_test")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

sh_test(
    name = "proxy_test",
    srcs = ["test.sh"],
    data = [
        "//oak_proxy/client",
        "//oak_proxy/server",
    ],
)
