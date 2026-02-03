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

"""Module extensions for Oak toolchains."""

load("//bazel/crates:aliasing_crates_repository.bzl", "aliasing_crates_repository", aliased_crates_repository_macro = "aliased_crates_repository")
load("//bazel/crates:patched_crates.bzl", load_patched_crates_macro = "load_patched_crates")

def _parse_crate_specs(content):
    """Robustly parses crate specifications from a string.

    This is a simplified Starlark-in-Starlark parser that handles the regular
    structure of our oak_crate_specs.MODULE.bazel file.
    """

    # Constants defined in the file
    STD = "oak_std_crates_index"
    NO_STD = "oak_no_std_crates_index"
    NO_STD_NO_AVX = "oak_no_std_no_avx_crates_index"
    ALL_REPOSITORIES = [STD, NO_STD, NO_STD_NO_AVX]
    ALL_NO_STD = [NO_STD, NO_STD_NO_AVX]
    ALL_STD = [STD]
    ONLY_NO_STD = [NO_STD]
    ONLY_NO_STD_NO_AVX = [NO_STD_NO_AVX]

    CONSTANTS = {
        "ALL_REPOSITORIES": ALL_REPOSITORIES,
        "ALL_NO_STD": ALL_NO_STD,
        "ALL_STD": ALL_STD,
        "ONLY_NO_STD": ONLY_NO_STD,
        "ONLY_NO_STD_NO_AVX": ONLY_NO_STD_NO_AVX,
    }

    crates_out = {r: {} for r in ALL_REPOSITORIES}

    # Split into crate.spec calls
    for call in content.split("crate.spec(")[1:]:
        call = call.strip()
        if not call:
            continue

        # Extract the block of arguments before the closing parenthesis
        if ")" not in call:
            # Skip if it's just some random text that happens to follow crate.spec(
            # but doesn't have a closing paren, but usually this is an error.
            # However, in our file, it might be a split issue.
            continue
        args_block = call.split(")", 1)[0]

        # Extract package name
        package = ""
        if "package =" in args_block:
            # Find the value after package =
            pkg_part = args_block.split("package =", 1)[1].strip()
            if pkg_part.startswith("\""):
                package = pkg_part.split("\"", 2)[1]
            elif pkg_part.startswith("'"):
                package = pkg_part.split("'", 2)[1]

        # Extract repositories
        repositories = []
        if "repositories =" in args_block:
            # Extract the word after repositories =
            repo_val = args_block.split("repositories =", 1)[1].strip().split(",", 1)[0].split("\n", 1)[0].strip()

            if repo_val in CONSTANTS:
                repositories = CONSTANTS[repo_val]
            else:
                fail("Unsupported value for repositories in crate.spec: \"{}\". Only predefined constants (e.g., ALL_REPOSITORIES) are supported. Literal lists are not allowed.".format(repo_val))

        # Only fail if it looks like a crate.spec but is missing fields.
        if not package or not repositories:
            if "package =" in args_block or "repositories =" in args_block:
                fail("Failed to parse crate.spec in oak_crate_specs.MODULE.bazel. Found package: \"{}\", repositories: {}. Ensure BOTH are present and follow the conventions described in the file.".format(package, repositories))
            continue

        for r in repositories:
            if r in crates_out:
                crates_out[r][package] = True

    return crates_out

def _aliased_crates_repository(ctx):
    spec_label = Label("//:MODULE.bazel")
    content = ctx.read(spec_label)

    crates = _parse_crate_specs(content)

    oak_std_crates = crates.get("oak_std_crates_index", {})
    oak_no_std_crates = crates.get("oak_no_std_crates_index", {})
    oak_no_std_no_avx_crates = crates.get("oak_no_std_no_avx_crates_index", {})

    # A workaround for dependencies that are transitionally using both WORKSAPCE
    # and MODULE.bazel to import Oak.
    # The toolchains will be set up expecting constraints defined by @@oak, but
    # the creates are set up earlier, before @@oak exists.
    repo_name = ""
    for m in ctx.modules:
        if m.name == "oak" and not m.is_root:
            repo_name = "@@oak"

    x86_64_none_label = Label("{}//:x86_64-none-setting".format(repo_name))
    wasm32_none_label = Label("{}//:wasm32-none-setting".format(repo_name))
    x86_64_none_no_avx_label = Label("{}//:x86_64-none-no_avx-setting".format(repo_name))

    aliasing_crates_repository(
        name = "oak_crates_index",
        repositories = [
            aliased_crates_repository_macro(
                name = "oak_no_std_crates_index",
                conditions = [x86_64_none_label, wasm32_none_label],
                packages = oak_no_std_crates.keys(),
                overrides = {
                    "prost-types": Label("@prost_types_oak_patched//:prost-types"),
                    "prost": Label("@prost_types_oak_patched//:prost"),
                },
            ),
            aliased_crates_repository_macro(
                name = "oak_no_std_no_avx_crates_index",
                conditions = [x86_64_none_no_avx_label],
                packages = oak_no_std_no_avx_crates.keys(),
                overrides = {
                    "prost-types": Label("@prost_types_oak_patched//:prost-types"),
                    "prost": Label("@prost_types_oak_patched//:prost"),
                },
            ),
            aliased_crates_repository_macro(
                name = "oak_std_crates_index",
                conditions = ["//conditions:default"],
                packages = oak_std_crates.keys(),
            ),
        ],
    )

aliased_crates_repository = module_extension(
    implementation = _aliased_crates_repository,
)

def _load_patched_crates_impl(_ctx):
    load_patched_crates_macro()

load_patched_crates = module_extension(
    implementation = _load_patched_crates_impl,
)
