#
# Copyright 2026 The Project Oak Authors
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

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_binary(
    name = "generate_policy",
    srcs = ["src/main.rs"],
    args = [
        "$(location //cleanroom/examples/to_uppercase:to_uppercase_wasm)",
        "$(location //cleanroom/examples/redact_secret:redact_secret_wasm)",
        "$(location //cleanroom/examples/weather:weather_wasm)",
        "$(location //cleanroom/examples/limited_calendar:limited_calendar_wasm)",
        "$(location //cleanroom/examples/crate_vendor:crate_vendor)",
    ],
    data = [
        "//cleanroom/examples/crate_vendor",
        "//cleanroom/examples/limited_calendar:limited_calendar_wasm",
        "//cleanroom/examples/redact_secret:redact_secret_wasm",
        "//cleanroom/examples/to_uppercase:to_uppercase_wasm",
        "//cleanroom/examples/weather:weather_wasm",
    ],
    deps = [
        "//cleanroom:cleanroom_lib",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:sha2",
    ],
)
