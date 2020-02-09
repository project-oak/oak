#
# Copyright 2019 The Project Oak Authors
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

load("@io_bazel_rules_docker//container:container.bzl", "container_image")
load("@com_google_asylo//asylo/bazel:asylo.bzl", "enclave_loader")
load("@com_google_asylo//asylo/bazel:copts.bzl", "ASYLO_DEFAULT_COPTS")
load("@linux_sgx//:sgx_sdk.bzl", "sgx")
load("@rules_cc//cc:defs.bzl", "cc_library")

package(
    default_visibility = [
        "//examples:__subpackages__",
        "//oak/server:__subpackages__",
    ],
    licenses = ["notice"],
)

cc_library(
    name = "enclave_server",
    srcs = [
        "enclave_server.cc",
    ],
    hdrs = [
        "enclave_server.h",
    ],
    deps = [
        "//oak/proto:enclave_cc_proto",
        "//oak/server:oak_runtime",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_asylo//asylo:enclave_runtime",
        "@com_google_asylo//asylo/grpc/auth:grpc++_security_enclave",
        "@com_google_asylo//asylo/grpc/auth:null_credentials_options",
        "@com_google_asylo//asylo/grpc/util:enclave_server_cc_proto",
        "@com_google_asylo//asylo/util:logging",
        "@com_google_asylo//asylo/util:status",
    ],
)

cc_library(
    name = "asylo_oak_loader",
    srcs = [
        "asylo_oak_loader.cc",
    ],
    hdrs = [
        "asylo_oak_loader.h",
    ],
    deps = [
        "//oak/proto:enclave_cc_proto",
        "//oak/proto:manager_cc_grpc",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/strings",
        "@com_google_asylo//asylo:enclave_client",
        "@com_google_asylo//asylo/grpc/util:enclave_server_cc_proto",
        "@com_google_asylo//asylo/identity:descriptions",
        "@com_google_asylo//asylo/identity:enclave_assertion_authority_config_cc_proto",
        "@com_google_asylo//asylo/util:logging",
    ],
)

sgx.enclave_configuration(
    name = "grpc_enclave_config",
    # gRPC needs more than the default amount of heap to run. ~1.2GB.
    heap_max_size = "0x47000000",
    tcs_num = "200",
)

sgx.unsigned_enclave(
    name = "oak_enclave_unsigned.so",
    srcs = [
        "oak_enclave.cc",
    ],
    copts = ASYLO_DEFAULT_COPTS,
    deps = [
        "//oak/server/asylo:enclave_server",
        "@com_google_asylo//asylo/grpc/util:enclave_server",
    ],
)

sgx.debug_enclave(
    name = "oak_enclave_debug.so",
    unsigned = ":oak_enclave_unsigned.so",
    config = ":grpc_enclave_config",
)

# Pulls the MRENCLAVE value from an enclave signing material.
# TODO: Use genrule from asylo, when it will become available.
genrule(
    name = "oak_mrenclave",
    srcs = [":oak_enclave_signing_material"],
    outs = ["oak_mrenclave.txt"],
    # Gets the enclave hash from the enclave signing material as a hex string.
    # Signing material consists of the header and the body of the SIGSTRUCT
    # struct (excluding keys), defined here:
    # https://github.com/intel/linux-sgx/blob/d10cabebb5512878e84f5d21cdf27c39c428ffe2/common/inc/internal/arch.h#L240-L245
    # Signing material generation is defined here:
    # https://github.com/intel/linux-sgx/blob/d10cabebb5512878e84f5d21cdf27c39c428ffe2/sdk/sign_tool/SignTool/sign_tool.cpp#L528-L548
    # 188 is an offset of the hash (instead of the original 960 from the SIGSTRUCT),
    # 32 is the size of the hash.
    cmd = "xxd -p -s 188 -l 32 -c 32 $< > $@",
)

# Generates an enclave dump that contains the MRSIGNER value.
genrule(
    name = "oak_enclave_debug_metadata",
    srcs = [":oak_enclave_debug.so"],
    outs = ["oak_enclave_debug_metadata.txt"],
    cmd = "$(location @linux_sgx//:sgx_sign_tool) dump -enclave $< -dumpfile $@",
    tools = ["@linux_sgx//:sgx_sign_tool"],
)

# Produces oak_enclave_sigstruct.dat file, which is used to generate the remote attestation of the
# enclave code. See https://software.intel.com/en-us/node/703003.
sgx.generate_enclave_signing_material(
    name = "oak_enclave_signing_material",
    unsigned = ":oak_enclave_unsigned.so",
    config = ":grpc_enclave_config",
)

enclave_loader(
    name = "asylo_oak_runner",
    srcs = ["asylo_oak_runner_main.cc"],
    enclaves = {"enclave": "//oak/server/asylo:oak_enclave_debug.so"},
    loader_args = ["--enclave_path='{enclave}'"],
    deps = [
        ":asylo_oak_loader",
        "//oak/common:app_config",
        "//oak/common:utils",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/flags:flag",
        "@com_google_absl//absl/flags:parse",
        "@com_google_absl//absl/synchronization",
        "@com_google_absl//absl/time",
        "@com_google_asylo//asylo/util:logging",
    ],
)

container_image(
    name = "oak_docker",
    base = "@cc_image//image",
    entrypoint = [
        "./oak_host_loader",
        "--enclave_path=oak_enclave_debug.so",
        "--grpc_port=8888",
    ],
    files = [
        "oak_enclave_debug.so",
        "oak_host_loader",
    ],
    ports = [
        # https://github.com/project-oak/oak/blob/667b07c555cde0c4705e5f7533b101203cc01c12/oak/server/asylo/asylo_oak_manager.cc#L48
        "8080/tcp",  # Oak Application gRPC port.
        # https://github.com/project-oak/oak/blob/667b07c555cde0c4705e5f7533b101203cc01c12/oak/server/asylo/asylo_oak_main.cc#L33
        "8888/tcp",  # Oak Manager gRPC port.
    ],
    repository = "gcr.io/oak-ci",
)

container_image(
    name = "oak_app_docker",
    base = "@cc_image//image",
    files = [
        "oak_app_host_loader",
        "oak_enclave_debug.so",
    ],
    ports = [
        "8080/tcp",  # Oak Application gRPC port.
    ],
    repository = "gcr.io/oak-ci",
)
