workspace(name = "oak")

# Download and use the Asylo SDK. Uncomment the sha256 line and replace with an
# appropriate hash to protect the integrity of your toolchain. It is commented
# out because this file is part of the hash computation.
http_archive(
    name = "com_google_asylo",
    urls = ["https://github.com/google/asylo/archive/v0.3.0.tar.gz"],
    strip_prefix = "asylo-0.3.0",
#   sha256 = "<insert hash here>",
)

load(
    "@com_google_asylo//asylo/bazel:asylo_deps.bzl",
    "asylo_deps",
    "asylo_go_deps",
    "asylo_testonly_deps",
)
asylo_deps()
asylo_testonly_deps()

load(
    "@com_google_asylo//asylo/bazel:sgx_deps.bzl",
    "sgx_deps",
)
sgx_deps()

load(
    "@com_github_grpc_grpc//bazel:grpc_deps.bzl",
    "grpc_deps",
)
grpc_deps()

# io_bazel_rules is defined by asylo_go_deps(). Skylark loads cannot be
# produced by macros, so this must come after asylo_go_deps() in WORKSPACE.
# We override the Go bazel rules to a release version that supports Go 1.11, since we need support
# for the wasm backend.
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
http_archive(
    name = "io_bazel_rules_go",
    urls = ["https://github.com/bazelbuild/rules_go/releases/download/0.16.1/rules_go-0.16.1.tar.gz"],
    sha256 = "f5127a8f911468cd0b2d7a141f17253db81177523e4429796e14d429f5444f5f",
)
load("@io_bazel_rules_go//go:def.bzl", "go_rules_dependencies", "go_register_toolchains")
go_rules_dependencies()
go_register_toolchains()
