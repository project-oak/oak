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
load("@npm//oak_trusted_agent/sandbox/guest/agent_ts:@bytecodealliance/componentize-js/package_json.bzl", componentize_js_bin = "bin")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_test")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

npm_link_all_packages(name = "node_modules")

ts_project(
    name = "agent_ts_lib",
    srcs = glob(
        ["src/**/*.ts"],
        exclude = ["src/*_test.ts"],
    ),
    declaration = True,
    target_compatible_with = ["@platforms//os:linux"],
    transpiler = "tsc",
    tsconfig = ":tsconfig.json",
    deps = [
        ":node_modules/@google/adk",
        ":node_modules/@types/node",
        ":node_modules/loglevel",
    ],
)

ts_project(
    name = "agent_ts_lib_test",
    testonly = True,
    srcs = glob(["src/*_test.ts"]) + ["src/types.d.ts"],
    declaration = True,
    extends = ":tsconfig.json",
    target_compatible_with = ["@platforms//os:linux"],
    transpiler = "tsc",
    tsconfig = {
        "exclude": [],
        "extends": "./tsconfig.json",
        "include": [
            "src/*_test.ts",
            "src/types.d.ts",
        ],
    },
    deps = [
        ":agent_ts_lib",
        ":node_modules/@google/adk",
        ":node_modules/@types/node",
        ":node_modules/loglevel",
    ],
)

esbuild(
    name = "agent_ts_bundle",
    srcs = glob(
        ["src/**/*.ts"],
        exclude = ["src/*_test.ts"],
    ) + [":agent_ts_lib"],
    config = "esbuild.config.mjs",
    entry_point = "src/index.ts",
    external = ["oak:agent/*"],
    format = "esm",
    output = "bundle.js",
    sourcemap = False,
    target = "es2022",
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        ":node_modules/@google/adk",
        ":node_modules/loglevel",
    ],
)

copy_to_directory(
    name = "staged_wit",
    srcs = ["//oak_trusted_agent/sandbox:wit_files"],
    root_paths = ["oak_trusted_agent/sandbox/wit"],
    target_compatible_with = ["@platforms//os:linux"],
)

componentize_js_bin.componentize_js_binary(
    name = "componentize_js_bin",
    node_options = ["--experimental-require-module"],
    target_compatible_with = ["@platforms//os:linux"],
)

# @bytecodealliance/componentize-js (version 0.22.0) enables default WASI features
# (DEFAULT_FEATURES = ['stdio', 'random', 'clocks', 'http', 'fetch-event']), which
# automatically splice wasi:cli, wasi:clocks, wasi:random, and wasi:http imports into
# the output component. Our minimal Oak agent interface only requires oak:agent/tools
# and oak:agent/model, so we explicitly disable all default WASI features.
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
        "--disable",
        "http",
        "--disable",
        "fetch-event",
        "--disable",
        "clocks",
        "--disable",
        "random",
        "--disable",
        "stdio",
        "-o",
        "adk_agent_ts.wasm",
    ],
    chdir = package_name(),
    mnemonic = "ComponentizeJs",
    tags = ["no-sandbox"],
    target_compatible_with = ["@platforms//os:linux"],
    tool = ":componentize_js_bin",
)

# Insecure/debug build of the agent Wasm component.
# Unlike the secure `adk_agent_ts` target which disables stdio, this target
# leaves WASI stdio enabled so that loglevel / console messages can be printed
# directly to the host console during development and debugging.
js_run_binary(
    name = "adk_agent_ts_insecure",
    srcs = [
        ":agent_ts_bundle",
        ":staged_wit",
    ],
    outs = ["adk_agent_ts_insecure.wasm"],
    args = [
        "bundle.js",
        "--wit",
        "staged_wit",
        "--world-name",
        "oak-agent",
        "--disable",
        "http",
        "--disable",
        "fetch-event",
        "--disable",
        "clocks",
        "--disable",
        "random",
        "-o",
        "adk_agent_ts_insecure.wasm",
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
    entry_point = "src/models_test.js",
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
    entry_point = "src/tools_test.js",
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
    entry_point = "src/agent_test.js",
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
        "src/types.d.ts",
        "//oak_trusted_agent/sandbox:wit/agent.wit",
    ],
    rustc_env = {
        "CHECKED_IN_TYPES": "$(rootpath src/types.d.ts)",
        "WIT_FILE": "$(rootpath //oak_trusted_agent/sandbox:wit/agent.wit)",
    },
    target_compatible_with = ["@platforms//os:linux"],
)

rust_test(
    name = "wit_types_sync_test",
    size = "small",
    crate = ":generate_wit_types",
    data = [
        "src/types.d.ts",
        "//oak_trusted_agent/sandbox:wit/agent.wit",
    ],
    rustc_env = {
        "CHECKED_IN_TYPES": "$(rootpath src/types.d.ts)",
        "WIT_FILE": "$(rootpath //oak_trusted_agent/sandbox:wit/agent.wit)",
    },
    target_compatible_with = ["@platforms//os:linux"],
)
