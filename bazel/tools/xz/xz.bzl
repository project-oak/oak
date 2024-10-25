#
# Copyright 2024 The Project Oak Authors
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
"""Rules for xz compression."""

def xz_compress(name, target, out, **kwargs):
    """ A quick non-hermetic xz rule.

    It requires having xz in your path.

    Args:
        name: the name of the output rule
        target: the target to compress. It should contain only one file output.
        out: the name of the generated xz-compressed file.
        **kwargs: any other args to pass to the genrule.
    """
    native.genrule(
        name = name,
        srcs = [target],
        outs = [out],
        cmd = "xz --force $(SRCS) --stdout > $(OUTS)",
        **kwargs
    )
