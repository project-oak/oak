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

load(
    "//oak_attestation_gcp/jwtgen:defs.bzl",
    "jwt_token",
    "rsa_key_pair",
    "x509_cert",
)

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

exports_files(glob(["*"]))

rsa_key_pair(name = "root_ca")

x509_cert(
    name = "root_ca_cert",
    days = 3650,
    faketime = "2025-01-01 00:00:00 UTC",
    signing_key = ":root_ca_private_key",
    subject = "/CN=Test Root CA",
)

rsa_key_pair(name = "signing")

x509_cert(
    name = "signing_cert",
    ca_cert = ":root_ca_cert",
    ca_key = ":root_ca_private_key",
    days = 365,
    faketime = "2025-01-01 00:00:00 UTC",
    signing_key = ":signing_private_key",
    subject = "/CN=Test Signer",
)

jwt_token(
    name = "token",
    claims = ":claims.json",
    root_ca_cert = ":root_ca_cert",
    signing_cert = ":signing_cert",
    signing_key = ":signing_private_key",
)
