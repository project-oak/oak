load("@aspect_bazel_lib//lib:copy_file.bzl", "copy_file")

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
load("@aspect_bazel_lib//lib:write_source_files.bzl", "write_source_files")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

# Copy the file to a nicely named spot.
copy_file(
    name = "kernel",
    src = "@nix_linux_kernel//:bzImage",
    out = "bzImage",
)

genrule(
    name = "generate_kernel_sha256",
    srcs = ["@nix_linux_kernel//:bzImage"],
    outs = ["bzImage.sha256"],
    cmd = "sha256sum $(location @nix_linux_kernel//:bzImage) > $@",
)

genrule(
    name = "generate_vanilla_kernel_sha256",
    srcs = ["@nix_vanilla_linux_kernel//:bzImage"],
    outs = ["vanilla_bzImage.sha256"],
    cmd = "sha256sum $(location @nix_vanilla_linux_kernel//:bzImage) > $@",
)

write_source_files(
    name = "regenerate_sha256",
    files = {
        "generated/bzImage.sha256": ":generate_kernel_sha256",
        "generated/vanilla_bzImage.sha256": ":generate_vanilla_kernel_sha256",
    },
)

genrule(
    name = "subjects",
    srcs = [
        "kernel",
        "//oak_kernel_measurement",
    ],
    outs = [
        "oak_containers_kernel_image",
        "oak_containers_kernel_setup_data",
    ],
    cmd = "$(location //oak_kernel_measurement) \
        --kernel=$(location :kernel) \
        --kernel-setup-data-output=$(@D)/oak_containers_kernel_setup_data \
        --kernel-image-output=$(@D)/oak_containers_kernel_image",
)
