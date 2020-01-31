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

"""Rule for serializing an Oak application configuration."""

<<<<<<< HEAD
def serialized_config(name, textproto, modules):
    """Serializes an Oak application configuration in a binary file.

    Implicit output targets:
        name.bin: A binary file with a serialized application configuration.

    Args:
        name: Name of the generated binary file (the output file will have a `.bin` extension).
        textproto: Textproto file with application configuration.
        modules: A dictionary with module names as keys and module paths as values.
    """
    srcs = [textproto] + modules.values()
    module_list = ",".join(["{}:$(location {})".format(name, path) for (name, path) in modules.items()])
    cmd = "$(location //oak/common:app_config_serializer)" + \
          " --textproto=$(location {})".format(textproto) + \
          " --modules={}".format(module_list) + \
          " --output_file=$@"
    native.genrule(
        name = name,
        srcs = srcs,
        # Name of the rule cannot be the same as the output file.
        outs = ["{}.bin".format(name)],
        cmd = cmd,
        tools = ["//oak/common:app_config_serializer"],
    )
