// Copyright 2025 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![feature(try_blocks)]

use jwt::{Token, Unverified};
use oak_attestation_gcp::{
    jwt::{verification::report_attestation_token, Claims, Header},
    CONFIDENTIAL_SPACE_ROOT_CERT_PEM,
};
use oak_proto_rust::oak::ctf_sha2::Input;
use prost::Message;
use sha2::{Digest, Sha256};
use x509_cert::{der::DecodePem, Certificate};

fn main() -> anyhow::Result<()> {
    let root_certificate =
        Certificate::from_pem(CONFIDENTIAL_SPACE_ROOT_CERT_PEM).map_err(anyhow::Error::msg)?;
    falsify::falsify(|input| {
        if let Ok(input) = Input::decode(input.as_slice()) {
            if let Ok(parsed_token) =
                Token::<Header, Claims, Unverified>::parse_unverified(&input.jwt)
            {
                // Here we trust the JWT issuance timestamp. This is a bit circular, but there
                // is no obvious better alternative which results in deterministic behaviour.
                let now = parsed_token.claims().issued_at;
                if let Ok(verified_token) =
                    report_attestation_token(parsed_token, &root_certificate, &now)
                        .into_checked_token()
                {
                    if let Ok(image_reference) = verified_token.claims().effective_reference() {
                        // Built at commit 74e81ae73c4a43d6cab10b3fb7c6ea43f0f2a3a5:
                        // $ git checkout 74e81ae73c4a43d6cab10b3fb7c6ea43f0f2a3a5 && \
                        //       bazel run ctf_sha2:image_push
                        if image_reference.digest() == Some("sha256:2e51b5f8db1e222a1c79d406718723a0d6121246511889dd5cd4c39f62d948c8") {
                            assert_ne!(compute_expected_flag_digest_string(&input.flag), verified_token.claims().eat_nonce);
                        }
                    }
                }
            }
        }
    });
    Ok(())
}

fn compute_expected_flag_digest_string(flag: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(flag);
    let expected_flag_digest = hasher.finalize();
    format!("{expected_flag_digest:x}")
}
