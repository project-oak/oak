# Build configuration to rebuild the rust std libraries.

load("@rules_rust//rust:defs.bzl", "rust_library")

package(default_visibility = ["//visibility:public"])

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
        "-Ccode-model=large",
    ],
    deps = [
        ":compiler_builtins",
        ":core",
    ],
)

rust_library(
    name = "compiler_builtins",
    srcs = glob([
        "vendor/compiler_builtins/src/**/*.rs",
        "vendor/compiler_builtins/libm/**/*.rs",
    ]),
    compile_data = glob(["vendor/compiler_builtins/src/**/*.md"]),
    crate_features = [
        "mem-unaligned",
        "compiler-builtins",
        "unstable",
        "no_std",
        "mem",
    ],
    crate_name = "compiler_builtins",
    edition = "2021",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        # TODO: b/359144829 - replace with select statement to support
        # panic_immeditate_abort.
        "--codegen=code-model=large",
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
        #"panic_immediate_abort",
        "no_std",
    ],
    crate_name = "core",
    edition = "2021",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        "-Ccode-model=large",
        #"-Cpanic=abort",
        "--cap-lints=allow",
        "-Zmacro-backtrace",
    ],
)

rust_library(
    name = "cfg_if",
    srcs = glob(["vendor/cfg-if/src/**/*.rs"]),
    compile_data = glob(["vendor/cfg-if/src/**/*.md"]),
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
        "-Ccode-model=large",
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
        "-Ccode-model=large",
        "-Cpanic=abort",
        "--cap-lints=allow",
        "-Zforce-unstable-if-unmarked",
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
    srcs = glob(["vendor/libc/src/**/*.rs"]),
    compile_data = glob(["vendor/libc/src/**/*.md"]),
    crate_features = [
        "align",
    ],
    crate_name = "libc",
    edition = "2021",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        "-Ccode-model=large",
        "--cfg=libc_align",
        "--cfg=libc_core_cvoid",
        "--cfg=libc_priv_mod_use",
        "--cfg=libc_const_extern_fn",
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
        "-Ccode-model=large",
        "-Zforce-unstable-if-unmarked",
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
    srcs = glob(["vendor/rustc-demangle/src/**/*.rs"]),
    compile_data = glob(["vendor/rustc-demangle/src/**/*.md"]),
    crate_features = [
        "core",
        "compiler_builtins",
        "no_std",
    ],
    crate_name = "rustc_demangle",
    crate_root = "vendor/rustc-demangle/src/lib.rs",
    rustc_env = {
        "RUSTC_BOOTSTRAP": "1",
    },
    rustc_flags = [
        "-Ccode-model=large",
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
        "-Ccode-model=large",
        "-Zforce-unstable-if-unmarked",
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
