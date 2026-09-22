#
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
#

load("@aspect_bazel_lib//lib:copy_to_directory.bzl", "copy_to_directory")
load("@aspect_rules_esbuild//esbuild:defs.bzl", "esbuild")
load("@aspect_rules_js//js:defs.bzl", "js_run_binary", "js_test")
load("@aspect_rules_ts//ts:defs.bzl", "ts_project")
load("@npm//:defs.bzl", "npm_link_all_packages")
load("@npm//oak_trusted_agent/sandbox:@bytecodealliance/componentize-js/package_json.bzl", componentize_js_bin = "bin")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_test")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

npm_link_all_packages(name = "node_modules")

filegroup(
    name = "wit_files",
    srcs = ["wit/agent.wit"],
)

ts_project(
    name = "agent_ts_lib",
    srcs = glob(
        ["agent_ts/src/**/*.ts"],
        exclude = ["agent_ts/src/*_test.ts"],
    ),
    declaration = True,
    target_compatible_with = ["@platforms//os:linux"],
    transpiler = "tsc",
    tsconfig = ":agent_ts/tsconfig.json",
    deps = [
        ":node_modules/@google/adk",
        ":node_modules/@types/node",
    ],
)

ts_project(
    name = "agent_ts_lib_test",
    testonly = True,
    srcs = glob(["agent_ts/src/*_test.ts"]) + ["agent_ts/src/types.d.ts"],
    declaration = True,
    extends = ":agent_ts/tsconfig.json",
    target_compatible_with = ["@platforms//os:linux"],
    transpiler = "tsc",
    tsconfig = {
        "exclude": [],
        "extends": "./agent_ts/tsconfig.json",
        "include": [
            "agent_ts/src/*_test.ts",
            "agent_ts/src/types.d.ts",
        ],
    },
    deps = [
        ":agent_ts_lib",
        ":node_modules/@google/adk",
        ":node_modules/@types/node",
    ],
)

esbuild(
    name = "agent_ts_bundle",
    srcs = glob(
        ["agent_ts/src/**/*.ts"],
        exclude = ["agent_ts/src/*_test.ts"],
    ) + [":agent_ts_lib"],
    config = "agent_ts/esbuild.config.mjs",
    entry_point = "agent_ts/src/index.ts",
    external = ["oak:agent/*"],
    format = "esm",
    output = "bundle.js",
    sourcemap = False,
    target = "es2022",
    target_compatible_with = ["@platforms//os:linux"],
    deps = [":node_modules/@google/adk"],
)

copy_to_directory(
    name = "staged_wit",
    srcs = [
        ":wit_files",
        "@wasi_snapshot_preview2//:wit_files",
    ],
    include_external_repositories = ["**"],
    replace_prefixes = {
        "wit/": "",
        "cli/": "deps/cli/",
        "clocks/": "deps/clocks/",
        "filesystem/": "deps/filesystem/",
        "http/": "deps/http/",
        "io/": "deps/io/",
        "random/": "deps/random/",
        "sockets/": "deps/sockets/",
    },
    target_compatible_with = ["@platforms//os:linux"],
)

componentize_js_bin.componentize_js_binary(
    name = "componentize_js_bin",
    node_options = ["--experimental-require-module"],
    target_compatible_with = ["@platforms//os:linux"],
)

js_run_binary(
    name = "adk_agent_ts",
    srcs = [
        ":agent_ts_bundle",
        ":staged_wit",
    ],
    outs = ["adk_agent_ts.wasm"],
    args = [
        "bundle.js",
        "--wit",
        "staged_wit",
        "--world-name",
        "oak-agent",
        "-o",
        "adk_agent_ts.wasm",
    ],
    chdir = package_name(),
    mnemonic = "ComponentizeJs",
    tags = ["no-sandbox"],
    target_compatible_with = ["@platforms//os:linux"],
    tool = ":componentize_js_bin",
)

# --conditions=browser instructs Node.js to resolve @google/adk's "browser" export
# condition (./dist/web/index_web.js), matching the self-contained web/Wasm bundle
# selected by esbuild rather than the unbundled Node entry point (./dist/esm/index.js),
# which imports undeclared transitive packages (e.g., 'uuid').
js_test(
    name = "models_test",
    size = "small",
    data = [":agent_ts_lib_test"],
    entry_point = "agent_ts/src/models_test.js",
    node_options = [
        "--conditions=browser",
        "--experimental-require-module",
    ],
    target_compatible_with = ["@platforms//os:linux"],
)

js_test(
    name = "tools_test",
    size = "small",
    data = [":agent_ts_lib_test"],
    entry_point = "agent_ts/src/tools_test.js",
    node_options = [
        "--conditions=browser",
        "--experimental-require-module",
    ],
    target_compatible_with = ["@platforms//os:linux"],
)

js_test(
    name = "agent_test",
    size = "small",
    data = [":agent_ts_lib_test"],
    entry_point = "agent_ts/src/agent_test.js",
    node_options = [
        "--conditions=browser",
        "--experimental-require-module",
    ],
    target_compatible_with = ["@platforms//os:linux"],
)

rust_binary(
    name = "generate_wit_types",
    srcs = ["generate_wit_types.rs"],
    data = [
        "agent_ts/src/types.d.ts",
        "wit/agent.wit",
    ],
    rustc_env = {
        "CHECKED_IN_TYPES": "$(rootpath agent_ts/src/types.d.ts)",
        "WIT_FILE": "$(rootpath wit/agent.wit)",
    },
    target_compatible_with = ["@platforms//os:linux"],
)

rust_test(
    name = "wit_types_sync_test",
    size = "small",
    crate = ":generate_wit_types",
    data = [
        "agent_ts/src/types.d.ts",
        "wit/agent.wit",
    ],
    rustc_env = {
        "CHECKED_IN_TYPES": "$(rootpath agent_ts/src/types.d.ts)",
        "WIT_FILE": "$(rootpath wit/agent.wit)",
    },
    target_compatible_with = ["@platforms//os:linux"],
)
