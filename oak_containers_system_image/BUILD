#
# Copyright 2023 The Project Oak Authors
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

load("@io_bazel_rules_docker//container:container.bzl", "container_image", "container_flatten")
load("@io_bazel_rules_docker//docker/util:run.bzl", "container_run_and_commit")


container_image(
    name = "oak_containers_system_image_base",
    base = "@clear_linux_amd64//image",
    files = [
        "//oak_containers_system_image/image_data:oak-orchestrator.service"
    ],
)

# Bootstrap the container image by installing some additional
# packages and running some post install commands
container_run_and_commit(
    name = "oak_containers_system_image",
    commands = [
        # Install Clear Linux's containers-basic bundle. This gives an installation of
        # docker to run containers. This is a starting point only, we should switch to
        # a more lightweight runtime later.
        # Ref: https://clearlinux.github.io/clear-linux-documentation/tutorials/docker.html#install-the-containers-basic-bundle
        "swupd bundle-add containers-basic",
        "systemctl enable docker",
        # Start the orchestartor a boot
        "mv /oak-orchestrator.service /lib/systemd/system/",
        "chmod 644 /lib/systemd/system/oak-orchestrator.service",
        "systemctl enable oak-orchestrator",
        # Don't bother starting the graphical interface, let's stick with the basic multi-user target.
        "rm /usr/lib/systemd/system/default.target",
        "ln -s /usr/lib/systemd/system/multi-user.target /usr/lib/systemd/system/default.target"
    ],
    image = ":oak_containers_system_image_base.tar",
)

# Merge the layers and export the container's rootfs
container_flatten(
    name = "oak_containers_system_image_rootfs",
    image = ":oak_containers_system_image_commit.tar",
)
