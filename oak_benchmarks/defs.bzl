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

"""Builds both sides of the comparison for the same instruction set."""

load("//bazel/rust:defs.bzl", "ENCLAVE_TARGET_CPU", "ENCLAVE_TARGET_FEATURES")

# The instruction set both benchmark binaries are compiled for: the enclave's,
# plus SHA-NI.
#
# SHA-NI is not in ENCLAVE_TARGET_FEATURES because the enclave has to boot on
# whatever machine a developer happens to have, and enabling it there emits SHA
# instructions unconditionally. The benchmark binaries are not like that. They
# are only ever run deliberately, on a host chosen for the measurement, so they
# can assume it.
#
# Without it the two sides are not comparable. `sha2` selects its SHA-NI
# backend by runtime CPUID dispatch, which works on the Linux baseline, while
# `cpufeatures` answers false without consulting CPUID at all when
# `target_os = "none"`, so the enclave never reaches that backend on any host.
# The difference is worth about 5x on SHA-256 and would otherwise be read as a
# cost of the restricted kernel.
BENCHMARK_TARGET_FEATURES = ENCLAVE_TARGET_FEATURES + ",+sha"

_BENCHMARK_RUSTC_FLAGS = [
    "--codegen=target-feature=" + BENCHMARK_TARGET_FEATURES,
    "--codegen=target-cpu=" + ENCLAVE_TARGET_CPU,
]

def _matched_isa_transition_impl(_settings, _attr):
    return {"@rules_rust//rust/settings:extra_rustc_flags": _BENCHMARK_RUSTC_FLAGS}

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
    doc = """Rebuilds a binary, and every crate it links, for the instruction
set the benchmark comparison is defined against.

Both sides need this, for opposite reasons. The standard Linux toolchain
passes no `target-feature` and no `target-cpu`, so it compiles for the base
x86-64 target while `bazel/rust/extensions.bzl` gives the `x86_64-unknown-none`
toolchain AVX2 and AES-NI: a baseline built the ordinary way vectorises the
memory kernels to a different width and makes `ahash` pick a different backend,
so the hash map benchmark would not even be hashing the same way on the two
sides. The enclave, in turn, is the side that misses SHA-NI, because the
bare-metal toolchain cannot enable it for every build of the repository. See
BENCHMARK_TARGET_FEATURES.

The flags go through a configuration transition rather than the target's own
`rustc_flags` because `rustc_flags` reaches only the crate it is set on, and
every one of those choices is made when the dependency is compiled.""",
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
