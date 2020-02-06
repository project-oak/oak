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

def serialized_config(name, textproto, modules):
    """Serializes an Oak application configuration in a binary file.

    Args:
        name: Name of the build rule.
        textproto: Textproto file with application configuration.
        modules: A dictionary with module names as keys and module paths as values.
    """
    srcs = [textproto] + modules.values()
    output = name + ".bin"
    module_list = ",".join([n + ":$(location " + path + ")" for (n, path) in modules.items()])
    cmd = "$(location //oak/common:app_config_serializer)" + \
          " --textproto=$(location " + textproto + ")" + \
          " --modules=" + module_list + \
          " --output_file=$@"
    native.genrule(
        name = name,
        srcs = srcs,
        outs = [output],
        cmd = cmd,
        tools = ["//oak/common:app_config_serializer"],
    )
