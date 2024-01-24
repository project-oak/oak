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

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

# These certificates are the root of trust of the AMD hardware verification
# chain: ARK -> ASK -> VCEK -> attestation report. The ARK and and ASK
# certificates are parameter-free (with the exception of the chip generation
# which is called `product name` elsewhere). They are valid until 2045 and
# can therefore be statically included. Since they are static it is sufficient
# to verify the ARK -> ASK validity offline in a unit test.
exports_files([
    "ark_genoa.pem",
    "ask_genoa.pem",
    "ark_milan.pem",
    "ask_milan.pem",
])
