#
# Copyright 2025 The Project Oak Authors
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

"""bzmod extensions for configuring nix pkgs."""

load("@rules_nixpkgs_core//:nixpkgs.bzl", "nixpkgs_local_repository")
load("//oak_containers/kernel:pkgs.bzl", "setup_nix_kernels")

# Flakes are not yet supported in bzlmod mode so we use this extension instead.
# See: https://github.com/tweag/rules_nixpkgs/issues/592
def _nix_repos_impl(_ctx):
    nixpkgs_local_repository(
        name = "nixpkgs",
        nix_file_deps = ["//:flake.lock"],
        nix_flake_lock_file = "//:flake.lock",
    )
    setup_nix_kernels()

nix_repos = module_extension(
    implementation = _nix_repos_impl,
)
