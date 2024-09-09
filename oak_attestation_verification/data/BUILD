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
#
# To verify ARK, redownload from https://www.amd.com/en/developer/sev.html and
# convert and compare against the repository copies. However, the mentioned
# URL uses a custom AMD format - the files used here can be obtained directly
# from https://kdsintf.amd.com/vcek/v1/${PRODUCT_NAME}/cert_chain, where
# PRODUCT_NAME is `Genoa` or `Milan`.
filegroup(
    name = "amd_ark_certs",
    srcs = [
        "ark_genoa.pem",
        "ark_milan.pem",
    ],
)

filegroup(
    name = "amd_ask_certs",
    srcs = [
        "ask_genoa.pem",
        "ask_milan.pem",
    ],
)
