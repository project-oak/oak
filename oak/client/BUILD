#
# Copyright 2018 Project Oak authors
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

cc_binary(
    name = "client",
    srcs = ["oak_client.cc"],
    deps = [
        "//oak/proto:oak_proto_cc",
        "//oak/proto:oak_server_grpc_proto",
        "@com_github_gflags_gflags//:gflags_nothreads",
        "@com_google_asylo//asylo/util:logging",
        "@com_google_asylo//asylo/identity:init",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_asylo//asylo/grpc/auth:null_credentials_options",
    ],
)
