#
# Copyright 2020 The Project Oak Authors
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

"""Rule for generating an Oak application Docker image."""

load("@io_bazel_rules_docker//container:container.bzl", "container_image")

def oak_docker(name, application, ports):
    """Generates an Oak application Docker image.

    An image contains an server runner and an application configuration file.

    Implicit output targets:
        name.tar: A TAR file with an archived Docker image.

    Args:
        name: Name of the generated docker image.
        application: Application configuration Bazel rule.
        ports: Ports that should be exposed in the corresponding Docker container.
    """
    application_path = "{}.bin".format(application)
    application_file = application_path.split(":")[-1]
    container_image(
        name = name,
        base = "//oak/server/loader:oak_docker",
        entrypoint = [
            "./oak_runner",
            "--application={}".format(application_file),
            "--ca_cert=ca.pem",
            "--cert_chain=docker.pem",
            "--private_key=docker.key",
        ],
        # `files` must contain full file paths with extensions.
        files = [application_path],
        ports = ports,
    )
