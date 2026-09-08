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

"""Bazel rules for creating Linux VM images for benchmarking."""

load("@rules_shell//shell:sh_binary.bzl", "sh_binary")

def vm_disk_image(
        name,
        binary,
        command = None,
        data = [],
        install_path = "/opt/app",
        extra_ip = None,
        visibility = None):
    """Creates a QCOW2 VM image with the specified binary pre-installed.

    The image is based on the Debian nocloud image defined in MODULE.bazel
    (@debian_nocloud_qcow2). The binary is installed to install_path and
    configured to run via a systemd service on boot.

    Args:
        name: Name of the target. The output will be {name}.qcow2.
        binary: Label of the binary to install in the VM.
        command: Command to run the binary (default: {install_path}/{binary_name}).
        data: Additional data files to install alongside the binary.
        install_path: Path where the binary is installed in the VM (default: /opt/app).
        extra_ip: Address in CIDR form to add to the guest's first non-loopback
            interface before the service starts, e.g. "198.18.0.2/30". Needed by
            run_vm.sh --net=tap, where there is no DHCP server; harmless under
            user networking, where it is simply unused.
        visibility: Visibility of the target.

    Example:
        vm_disk_image(
            name = "my_server_vm",
            binary = ":my_server",
            command = "/opt/app/my_server --port 5000",
            data = [":config_file"],
        )
    """

    # Determine binary name for default command
    binary_name = Label(binary).name
    effective_command = command if command else "{}/{}".format(install_path, binary_name)

    # Build the data files arguments
    data_args = ""
    for d in data:
        data_args += " --data=$(location {})".format(d)

    extra_ip_arg = " --extra-ip={}".format(extra_ip) if extra_ip else ""

    native.genrule(
        name = name,
        srcs = [
            "@debian_nocloud_qcow2//file",
            binary,
        ] + data,
        outs = [name + ".qcow2"],
        tools = ["//oak_benchmarks/linux_vm:prepare_image.sh"],
        cmd = """
$(location //oak_benchmarks/linux_vm:prepare_image.sh) \
    --binary=$(location {binary}) \
    --base-image=$(location @debian_nocloud_qcow2//file) \
    --output=$@ \
    --command="{command}" \
    --install-path="{install_path}"{data_args}{extra_ip_arg}
""".format(
            binary = binary,
            command = effective_command,
            install_path = install_path,
            data_args = data_args,
            extra_ip_arg = extra_ip_arg,
        ),
        visibility = visibility,
        # This rule requires guestfish which may not be available in all environments
        tags = [
            "local",
            "manual",
            "no-sandbox",
        ],
    )

    # Automatically generate a `<name>_run` target to execute the benchmark.
    sh_binary(
        name = name + "_run",
        srcs = ["//oak_benchmarks/linux_vm:run_linux_cli.sh"],
        data = [
            ":" + name,
            "//oak_benchmarks/linux_cli:linux_cli",
            "//oak_benchmarks/linux_vm:run_vm.sh",
        ],
        args = [
            "$(location //oak_benchmarks/linux_cli:linux_cli)",
            "$(location :" + name + ")",
            "$(location //oak_benchmarks/linux_vm:run_vm.sh)",
        ],
        tags = ["manual"],
        visibility = visibility,
    )
