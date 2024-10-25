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

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

# Stage1 binary.
rust_binary(
    name = "oak_containers_stage1",
    srcs = glob(["src/**"]),
    deps = [
        "//oak_attestation",
        "//oak_attestation_types",
        "//oak_containers/channel",
        "//oak_containers/stage1_dice",
        "//oak_dice",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:futures-util",
        "@oak_crates_index//:nix",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rtnetlink",
        "@oak_crates_index//:tar",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:x86_64",
        "@oak_crates_index//:xz2",
        "@oak_crates_index//:zerocopy",
        "@oak_crates_index//:zeroize",
    ],
)

alias(
    name = "stage1",
    actual = ":stage1_cpio",
)

# Oak Containers Initial RAM Filesystem.
genrule(
    name = "stage1_cpio",
    srcs = [
        ":oak_containers_stage1",
        "@e2fsprogs//:mke2fs",
        "@oak_cc_toolchain_sysroot//:linker_library",
        "@oak_cc_toolchain_sysroot//:stage1_shared_libraries",
    ],
    outs = [
        "stage1.cpio",
    ],
    cmd = """
        # Copy linker.
        mkdir --parents $(RULEDIR)/root/lib64
        cp $(location @oak_cc_toolchain_sysroot//:linker_library) $(RULEDIR)/root/lib64/

        # Copy shared libraries.
        mkdir --parents $(RULEDIR)/root/usr/lib/x86_64-linux-gnu
        cp $(locations @oak_cc_toolchain_sysroot//:stage1_shared_libraries) $(RULEDIR)/root/usr/lib/x86_64-linux-gnu/

        # Copy the mke2fs binary.
        cp --dereference --recursive $(locations @e2fsprogs//:mke2fs) $(RULEDIR)/root/

        # Strip and rename the oak_containers_stage1 binary.
        strip $(location :oak_containers_stage1) -o $(RULEDIR)/root/init

        # Create the compressed CPIO archive.
        (cd $(RULEDIR)/root && find .) | sort | \
            cpio --create --owner=root:root --format=newc --verbose --reproducible \
            --directory=$(RULEDIR)/root > $(RULEDIR)/stage1.cpio.tmp
        strip-nondeterminism --type=cpio --timestamp=0 $(RULEDIR)/stage1.cpio.tmp
        gzip --best --no-name $(RULEDIR)/stage1.cpio.tmp
        mv $(RULEDIR)/stage1.cpio.tmp.gz $(RULEDIR)/stage1.cpio
    """,
)
