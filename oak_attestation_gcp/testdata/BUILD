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
    "ecdsa_p256_key_pair",
    "jwt_token",
    "rsa_key_pair",
    "sign_file",
    "x509_cert",
)

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

exports_files(glob(["*"]))

# Create a root CA
rsa_key_pair(name = "root_ca")

x509_cert(
    name = "root_ca_cert",
    days = 3650,
    faketime = "2025-01-01 00:00:00 UTC",
    signing_key = ":root_ca_private_key",
    subject = "/CN=Test Root CA",
)

# Create a signing key and cert, signed by the root CA
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

# A valid token
jwt_token(
    name = "valid_token",
    claims = ":claims.json",
    root_ca_cert = ":root_ca_cert",
    signing_cert = ":signing_cert",
    signing_key = ":signing_private_key",
)

# A token with an invalid signature. We use a different signing key.
rsa_key_pair(name = "other_signing")

jwt_token(
    name = "invalid_signature_token",
    claims = ":claims.json",
    root_ca_cert = ":root_ca_cert",
    signing_cert = ":signing_cert",
    signing_key = ":other_signing_private_key",
)

# A token that is valid for a long time, signed by a short-lived cert.
jwt_token(
    name = "long_lived_token",
    claims = ":long_lived_claims.json",
    root_ca_cert = ":root_ca_cert",
    signing_cert = ":signing_cert",
    signing_key = ":signing_private_key",
)

# An expired token.
jwt_token(
    name = "expired_token",
    claims = ":expired_claims.json",
    root_ca_cert = ":root_ca_cert",
    signing_cert = ":signing_cert",
    signing_key = ":signing_private_key",
)

# An token from a debug image.
jwt_token(
    name = "debug_token",
    claims = ":debug_claims.json",
    root_ca_cert = ":root_ca_cert",
    signing_cert = ":signing_cert",
    signing_key = ":signing_private_key",
)

# A key pair for signing endorsements.
ecdsa_p256_key_pair(name = "developer_key")

sign_file(
    name = "endorsement_signature",
    file_to_sign = ":endorsement.json",
    signing_key = ":developer_key_private_key",
)

# A different key pair for signing endorsements.
ecdsa_p256_key_pair(name = "other_developer_key")

sign_file(
    name = "other_endorsement_signature",
    file_to_sign = ":endorsement.json",
    signing_key = ":other_developer_key_private_key",
)
