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
"""Rules related to android targets."""

def oak_jvm_jni_library(**kwargs):
    """A trivial macro to create targets destined for internal JVM use.

    This is currently just a simple wrapper around cc_binary.

    Its current purpose is to serve as an indication that we'd like to transform
    this rules into a specific JVM JNI rule in the import environment.
    """
    native.cc_binary(**kwargs)
