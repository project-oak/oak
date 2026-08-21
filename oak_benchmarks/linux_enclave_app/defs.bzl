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

"""Builds the Linux baseline with the enclave's instruction set."""

load("//bazel/rust:defs.bzl", "ENCLAVE_TARGET_CPU", "ENCLAVE_TARGET_FEATURES")

_ENCLAVE_RUSTC_FLAGS = [
    "--codegen=target-feature=" + ENCLAVE_TARGET_FEATURES,
    "--codegen=target-cpu=" + ENCLAVE_TARGET_CPU,
]

def _matched_isa_transition_impl(_settings, _attr):
    return {"@rules_rust//rust/settings:extra_rustc_flags": _ENCLAVE_RUSTC_FLAGS}

_matched_isa_transition = transition(
    inputs = [],
    outputs = ["@rules_rust//rust/settings:extra_rustc_flags"],
    implementation = _matched_isa_transition_impl,
)

def _matched_isa_binary_impl(ctx):
    info = ctx.attr.binary[DefaultInfo]
    out = ctx.actions.declare_file(ctx.label.name)
    ctx.actions.symlink(
        output = out,
        target_file = info.files_to_run.executable,
        is_executable = True,
    )
    return [DefaultInfo(
        executable = out,
        files = depset([out]),
        runfiles = info.default_runfiles,
    )]

matched_isa_binary = rule(
    doc = """Rebuilds a binary, and every crate it links, with the instruction
set the bare-metal enclave toolchain uses.

The standard Linux toolchain passes no `target-feature` and no `target-cpu`,
so it compiles for the base x86-64 target, while `bazel/rust/extensions.bzl`
gives the `x86_64-unknown-none` toolchain AVX2 and AES-NI. A baseline built
the ordinary way is therefore compiled differently from the enclave it is
measured against: the memory kernels vectorise to a different width, and
`ahash` selects a different backend, so the hash map benchmark would not even
be hashing the same way on the two sides.

The flags go through a configuration transition rather than the target's own
`rustc_flags` because `rustc_flags` reaches only the crate it is set on, and
both of those choices are made when the dependency is compiled.

SHA-NI is deliberately absent, matching the bare-metal toolchain: not every
machine that builds this repository has it.""",
    implementation = _matched_isa_binary_impl,
    executable = True,
    attrs = {
        "binary": attr.label(
            doc = "The binary to rebuild.",
            mandatory = True,
            executable = True,
            cfg = "target",
        ),
        "_allowlist_function_transition": attr.label(
            default = Label("@bazel_tools//tools/allowlists/function_transition_allowlist"),
        ),
    },
    cfg = _matched_isa_transition,
)
