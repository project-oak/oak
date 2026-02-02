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
"""Defines a toolchain rule for umoci."""

UmociInfo = provider(
    doc = "Information about how to invoke the umoci tool.",
    fields = {
        "bin": "Executable umoci binary",
    },
)

def _umoci_toolchain_impl(ctx):
    binary = ctx.file.bin
    default_info = DefaultInfo(
        files = depset([binary]),
        runfiles = ctx.runfiles(files = [binary]),
    )
    toolchain_info = platform_common.ToolchainInfo(
        umociinfo = UmociInfo(
            bin = binary,
        ),
    )
    return [default_info, toolchain_info]

umoci_toolchain = rule(
    implementation = _umoci_toolchain_impl,
    attrs = {
        "bin": attr.label(
            allow_single_file = True,
            executable = True,
            mandatory = True,
            cfg = "exec",
        ),
    },
)

def _umoci_toolchain_repo_impl(repository_ctx):
    repository_ctx.download(
        url = "https://github.com/opencontainers/umoci/releases/download/v0.4.7/umoci.amd64",
        output = "umoci.amd64",
        executable = True,
        sha256 = "6abecdbe7ac96a8e48fdb73fb53f08d21d4dc5e040f7590d2ca5547b7f2b2e85",
    )

    repository_ctx.symlink(
        Label("//bazel/tools/umoci:umoci_toolchain.bzl"),
        "umoci_toolchain.bzl",
    )

    repository_ctx.template(
        "BUILD",
        repository_ctx.attr._build_tpl,
        executable = False,
    )

umoci_toolchain_repo = repository_rule(
    implementation = _umoci_toolchain_repo_impl,
    attrs = {
        "_build_tpl": attr.label(default = "//bazel/tools/umoci:BUILD.tpl"),
    },
)
