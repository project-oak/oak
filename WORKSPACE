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
asylo_go_deps()
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
load(
    "@io_bazel_rules_go//go:def.bzl",
    "go_rules_dependencies",
    "go_register_toolchains",
)
# Load go bazel rules and toolchain.
go_rules_dependencies()
go_register_toolchains()
