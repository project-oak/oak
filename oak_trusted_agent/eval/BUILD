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

load("@oak_trusted_agent_eval_pip//:requirements.bzl", "requirement")
load("@rules_oci//oci:defs.bzl", "oci_image", "oci_push")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_python//python:defs.bzl", "py_binary")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

exports_files(["requirements.txt"])

py_binary(
    name = "run",
    srcs = glob([
        "harness/**/*.py",
        "benchmarks/**/*.py",
    ]),
    imports = ["."],
    main = "harness/run.py",
    tags = ["manual"],
    deps = [
        requirement("agentdojo"),
        requirement("google-cloud-storage"),
        requirement("ollama"),
        requirement("openai"),
        requirement("pydantic"),
    ],
)

pkg_tar(
    name = "harness_tar",
    srcs = [":run"],
    include_runfiles = True,
    package_dir = "/workspace",
    tags = ["manual"],
    target_compatible_with = ["@platforms//os:linux"],
)

# /bin is a symlink to usr/bin in Ubuntu 24.04; target /usr/bin so the layer does not replace the symlink.
pkg_tar(
    name = "eval_bin_tar",
    srcs = [
        "entrypoint.sh",
        "//oak_trusted_agent/provenance/signer:oak_trusted_agent_provenance_signer",
    ],
    package_dir = "/usr/bin",
    remap_paths = {
        "/oak_trusted_agent_provenance_signer": "/signer",
    },
    target_compatible_with = ["@platforms//os:linux"],
)

oci_image(
    name = "eval_base",
    base = "@ollama_linux_amd64",
    entrypoint = ["/bin/entrypoint.sh"],
    env = {
        "OLLAMA_DEBUG": "false",
        "OLLAMA_HOST": "127.0.0.1:11434",
        # Keep model weights loaded in memory indefinitely (default is 5m).
        "OLLAMA_KEEP_ALIVE": "-1",
        "OLLAMA_MODELS": "/models",
        "PATH": "/workspace/run.runfiles/rules_python++python+python_3_11_x86_64-unknown-linux-gnu/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONHASHSEED": "42",
        "PYTHONUNBUFFERED": "1",
    },
    # Omit allow_cmd_override so callers cannot sign arbitrary commands under this image digest.
    labels = {
        "tee.launch_policy.allow_env_override": "CONTAINER_IMAGE,BENCHMARK,RESULTS_BUCKET",
        "tee.launch_policy.log_redirect": "always",
    },
    tags = ["manual"],
    target_compatible_with = ["@platforms//os:linux"],
    tars = [
        ":eval_bin_tar",
        ":harness_tar",
    ],
    workdir = "/workspace",
)

oci_image(
    name = "image_gemma4_e2b_it_qat",
    base = ":eval_base",
    env = {
        "OLLAMA_MODEL": "gemma4:e2b-it-qat",
    },
    tags = ["manual"],
    target_compatible_with = ["@platforms//os:linux"],
    tars = ["@ollama_gemma4_e2b_it_qat//:layers"],
)

oci_push(
    name = "push_gemma4_e2b_it_qat",
    image = ":image_gemma4_e2b_it_qat",
    remote_tags = ["latest"],
    repository = "us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/eval/gemma4-e2b-it-qat",
    tags = ["manual"],
    target_compatible_with = ["@platforms//os:linux"],
)
