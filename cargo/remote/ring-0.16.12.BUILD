"""
cargo-raze crate build file.

DO NOT EDIT! Replaced on runs of cargo-raze
"""
package(default_visibility = [
  # Public for visibility by "@raze__crate__version//" targets.
  #
  # Prefer access through "//cargo", which limits external
  # visibility to explicit Cargo.toml dependencies.
  "//visibility:public",
])

licenses([
  "restricted", # "no license"
])

load(
    "@io_bazel_rules_rust//rust:rust.bzl",
    "rust_library",
    "rust_binary",
    "rust_test",
)

rust_binary(
    name = "ring_build_script",
    srcs = glob(["**/*.rs"]),
    crate_root = "build.rs",
    edition = "2018",
    deps = [
        "@raze__cc__1_0_52//:cc",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    crate_features = [
      "alloc",
      "default",
      "dev_urandom_fallback",
      "lazy_static",
    ],
    data = glob(["*"]),
    version = "0.16.12",
    visibility = ["//visibility:private"],
)

genrule(
    name = "ring_build_script_executor",
    srcs = glob(["*", "**/*.rs"]),
    outs = ["ring_out_dir_outputs.tar.gz"],
    tools = [
      ":ring_build_script",
    ],
    tags = ["no-sandbox"],
    cmd = "mkdir -p ring_out_dir_outputs/;"
        + " (export CARGO_MANIFEST_DIR=\"$$PWD/$$(dirname $(location :Cargo.toml))\";"
        + " export TARGET='x86_64-unknown-linux-gnu';"
        + " export RUST_BACKTRACE=1;"
        + " export CARGO_FEATURE_ALLOC=1;"
        + " export CARGO_FEATURE_DEFAULT=1;"
        + " export CARGO_FEATURE_DEV_URANDOM_FALLBACK=1;"
        + " export CARGO_FEATURE_LAZY_STATIC=1;"
        + " export CARGO_PKG_NAME=ring;"
        + " export CARGO_CFG_TARGET_ARCH=x86_64;"
        + " export CARGO_CFG_TARGET_OS=linux;"
        + " export CARGO_CFG_TARGET_ENV=musl;"
        + " export OPT_LEVEL=3;"
        + " export DEBUG=false;"
        + " export HOST=any;"
        + " export OUT_DIR=$$PWD/ring_out_dir_outputs;"
        + " export BINARY_PATH=\"$$PWD/$(location :ring_build_script)\";"
        + " export OUT_TAR=$$PWD/$@;"
        + " cd $$(dirname $(location :Cargo.toml)) && echo TEST && pwd && (echo OUT_DIR $$OUT_DIR) && $$BINARY_PATH && tar -czf $$OUT_TAR -C $$OUT_DIR .)"
)

# Unsupported target "aead_tests" with type "test" omitted
# Unsupported target "agreement_tests" with type "test" omitted
# Unsupported target "digest_tests" with type "test" omitted
# Unsupported target "ecdsa_tests" with type "test" omitted
# Unsupported target "ed25519_tests" with type "test" omitted
# Unsupported target "hkdf_tests" with type "test" omitted
# Unsupported target "hmac_tests" with type "test" omitted
# Unsupported target "pbkdf2_tests" with type "test" omitted
# Unsupported target "quic_tests" with type "test" omitted
# Unsupported target "rand_tests" with type "test" omitted

rust_library(
    name = "ring",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__lazy_static__1_4_0//:lazy_static",
        "@raze__libc__0_2_69//:libc",
        "@raze__spin__0_5_2//:spin",
        "@raze__untrusted__0_7_0//:untrusted",
    ],
    rustc_flags = [
        "--cap-lints=allow",
        "-lstatic=ring-core",
        "-Lnative=../../../../../execroot/oak/ring_out_dir_outputs/",
    ],
    out_dir_tar = ":ring_build_script_executor",
    data = glob(["**/*.der"]),
    version = "0.16.12",
    crate_features = [
        "alloc",
        "default",
        "dev_urandom_fallback",
        "lazy_static",
    ],
)

# Unsupported target "rsa_tests" with type "test" omitted
# Unsupported target "signature_tests" with type "test" omitted
