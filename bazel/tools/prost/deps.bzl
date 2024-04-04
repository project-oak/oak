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
"""Macros to setup the rust proto toolchains dependencies."""

load("@rules_rust//crate_universe:defs.bzl", "crate", "crates_repository")

def prost_toolchain_crates():
    """Define the creates_repository needed for the rust_prost_library toolchain."""

    crates_repository(
        name = "prost_toolchain_crates",
        annotations = {
            "protoc-gen-prost": [crate.annotation(
                gen_binaries = ["protoc-gen-prost"],
                patch_args = [
                    "-p1",
                ],
                patches = [
                    # Note: You will need to use this patch until a version greater than `0.2.2` of
                    # `protoc-gen-prost` is released.
                    #"@rules_rust//proto/prost/private/3rdparty/patches:protoc-gen-prost.patch",
                ],
            )],
            "protoc-gen-tonic": [crate.annotation(
                gen_binaries = ["protoc-gen-tonic"],
            )],
        },
        cargo_lockfile = "//:cargo-prost-bazel-lock.json",
        packages = {
            "prost": crate.spec(
                version = "*",
            ),
            "prost-types": crate.spec(
                version = "*",
            ),
            "protoc-gen-prost": crate.spec(
                version = "*",
            ),
            "protoc-gen-tonic": crate.spec(
                version = "*",
            ),
            "tonic": crate.spec(
                version = "*",
            ),
        },
        tags = ["manual"],
    )
