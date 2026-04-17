# Build configuration to rebuild the rust std libraries.

load("@oak//bazel/rust:defs.bzl", "STDLIBS_DEPS_VERSIONS")
load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

exports_files(["bin/*"])

filegroup(
    name = "binaries",
    srcs = glob([
        "bin/*",
        "lib/*",
        "lib64/*",
    ]),
)

filegroup(
    name = "stdlib_sources",
    srcs = [
        ":alloc",
        ":cfg_if",
        ":compiler_builtins",
        ":core",
        ":libc",
        ":panic_abort",
        ":rustc_demangle",
        ":unwind",
    ],
)

rust_library(
    name = "alloc",
    srcs = glob(["library/alloc/src/**/*.rs"]),
    compile_data = glob(["library/alloc/src/**/*.md"]),
    crate_features = ["no_std"],
    crate_name = "alloc",
    edition = "2021",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        "--codegen=code-model=large",
        "--codegen=relocation-model=static",
    ],
    deps = [
        ":compiler_builtins",
        ":core",
    ],
)

rust_library(
    name = "compiler_builtins",
    # There are multiple versions available in the nightly tarball, we choose the newest.
    srcs = glob([
        "vendor/compiler_builtins-" + STDLIBS_DEPS_VERSIONS["compiler_builtins"] + "/src/**/*.rs",
        "vendor/compiler_builtins-" + STDLIBS_DEPS_VERSIONS["compiler_builtins"] + "/libm/**/*.rs",
    ]),
    compile_data = glob(["vendor/compiler_builtins-0.1.123/src/**/*.md"]),
    crate_features = [
        "compiler-builtins",
        "force-soft-floats",
        "mem",
        "mem-unaligned",
        "no_std",
        "unstable",
    ],
    crate_name = "compiler_builtins",
    edition = "2021",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        "--codegen=code-model=large",
        "--codegen=relocation-model=static",
    ],
    deps = [":core"],
)

rust_library(
    name = "core",
    srcs = glob([
        "library/core/src/**/*.rs",
        "library/stdarch/crates/core_arch/src/**/*.rs",
        "library/portable-simd/crates/core_simd/src/**/*.rs",
    ]),
    compile_data = glob([
        "library/core/src/**/*.md",
        "library/core/primitive_docs/*.md",
        "library/stdarch/crates/core_arch/src/**/*.md",
        "library/portable-simd/crates/core_simd/src/**/*.md",
    ]),
    crate_features = [
        "no_std",
    ],
    crate_name = "core",
    edition = "2021",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        "--codegen=relocation-model=static",
        "--codegen=code-model=large",
        "--cap-lints=allow",
        "-Zmacro-backtrace",
    ],
)

rust_library(
    name = "cfg_if",
    # There are multiple versions available in the nightly tarball, we choose the newest.
    srcs = glob(["vendor/cfg-if-" + STDLIBS_DEPS_VERSIONS["cfg-if"] + "/src/**/*.rs"]),
    compile_data = glob(["vendor/cfg-if-" + STDLIBS_DEPS_VERSIONS["cfg-if"] + "/src/**/*.md"]),
    crate_features = [
        "compiler_builtins",
        "core",
        "no_std",
    ],
    crate_name = "cfg_if",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        "--codegen=code-model=large",
        "--codegen=relocation-model=static",
    ],
    deps = [
        ":compiler_builtins",
        ":core",
    ],
)

rust_library(
    name = "panic_abort",
    srcs = glob(["library/panic_abort/src/**/*.rs"]),
    compile_data = glob(["library/panic_abort/src/**/*.md"]),
    crate_features = [
        "no_std",
    ],
    crate_name = "panic_abort",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        "--codegen=code-model=large",
        "--codegen=panic=abort",
        "--cap-lints=allow",
        "-Zforce-unstable-if-unmarked",
        "--codegen=relocation-model=static",
    ],
    deps = [
        ":alloc",
        ":cfg_if",
        ":compiler_builtins",
        ":core",
        ":libc",
    ],
)

rust_library(
    name = "libc",
    # There are multiple versions available in the nightly tarball, we choose the newest.
    srcs = glob(["vendor/libc-" + STDLIBS_DEPS_VERSIONS["libc"] + "/src/**/*.rs"]),
    compile_data = glob(["vendor/libc-" + STDLIBS_DEPS_VERSIONS["libc"] + "/src/**/*.md"]),
    crate_features = [
        "align",
    ],
    crate_name = "libc",
    edition = "2021",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        "--codegen=code-model=large",
        "--cfg=libc_align",
        "--cfg=libc_core_cvoid",
        "--cfg=libc_priv_mod_use",
        "--cfg=libc_const_extern_fn",
        "--codegen=relocation-model=static",
    ],
    deps = [
        ":cfg_if",
        ":compiler_builtins",
        ":core",
    ],
)

rust_library(
    name = "unwind",
    srcs = glob(["library/unwind/src/**/*.rs"]),
    compile_data = glob(["library/unwind/src/**/*.md"]),
    crate_features = [
        "no_std",
        "llvm-libunwind",
    ],
    crate_name = "unwind",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        "--codegen=code-model=large",
        "-Zforce-unstable-if-unmarked",
        "--codegen=relocation-model=static",
    ],
    deps = [
        ":cfg_if",
        ":compiler_builtins",
        ":core",
        ":libc",
    ],
)

rust_library(
    name = "rustc_demangle",
    srcs = glob(["vendor/rustc-demangle-0.1.24/src/**/*.rs"]),
    compile_data = glob(["vendor/rustc-demangle-0.1.24/src/**/*.md"]),
    crate_features = [
        "core",
        "compiler_builtins",
        "no_std",
    ],
    crate_name = "rustc_demangle",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        "--codegen=code-model=large",
        "--codegen=relocation-model=static",
    ],
    deps = [
        ":compiler_builtins",
        ":core",
    ],
)

rust_library(
    name = "panic_unwind",
    srcs = glob(["library/panic_unwind/src/**/*.rs"]),
    compile_data = glob(["library/panic_unwind/src/**/*.md"]),
    crate_features = [
        "no_std",
    ],
    crate_name = "panic_unwind",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        "--codegen=code-model=large",
        "-Zforce-unstable-if-unmarked",
        "--codegen=relocation-model=static",
    ],
    deps = [
        ":alloc",
        ":cfg_if",
        ":compiler_builtins",
        ":core",
        ":libc",
        ":unwind",
    ],
)
