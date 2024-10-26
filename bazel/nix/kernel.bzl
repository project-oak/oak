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
"""Properly expose nix kernel to Bazel

In most contexts in Bazel, we can't access ambient environment variables. But in
a repository_rule, we can. So here we can "properly" expose the nix-built
kernels to Bazel, using the environment variables that we provide in flake.nix.
"""

def _nix_kernel_repo_impl(repository_ctx):
    kernel_path = repository_ctx.os.environ["LINUX_KERNEL"]
    vanilla_kernel_path = repository_ctx.os.environ["VANILLA_LINUX_KERNEL"]

    if not kernel_path:
        fail("Environment variable 'LINUX_KERNEL' is not set.")

    if not vanilla_kernel_path:
        fail("Environment variable 'VANILLA_LINUX_KERNEL' is not set.")

    repository_ctx.download(
        "file:///%s/bzImage" % kernel_path,
        sha256 = repository_ctx.attr.bzImage_sha256,
        output = "bzImage",
    )
    repository_ctx.download(
        "file:///%s/bzImage" % vanilla_kernel_path,
        sha256 = repository_ctx.attr.bzImage_vanilla_sha256,
        output = "bzImage_vanilla",
    )

    repository_ctx.file("BUILD", """
exports_files(
    srcs = ["bzImage", "bzImage_vanilla"]
)
    """)

nix_kernel_repo = repository_rule(
    implementation = _nix_kernel_repo_impl,
    local = True,
    attrs = {
        "bzImage_sha256": attr.string(mandatory = False),
        "bzImage_vanilla_sha256": attr.string(mandatory = False),
    },
)
