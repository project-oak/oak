//
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
//
use oak_proto_rust::oak::attestation::v1::ConfidentialSpaceReferenceValues;
use x509_cert::{der::DecodePem, Certificate};

use crate::{cosign::CosignReferenceValues, policy::ConfidentialSpacePolicy};

// Allways generates a policy that verifies whether the workload is running on
// Confidential Space. By extension, `root_certificate_pem` must always be
// specified.
pub fn confidential_space_policy_from_reference_values(
    reference_values: &ConfidentialSpaceReferenceValues,
) -> anyhow::Result<ConfidentialSpacePolicy> {
    let root_certificate = Certificate::from_pem(&reference_values.root_certificate_pem)
        .map_err(anyhow::Error::msg)?;

    if reference_values.cosign_reference_values.is_none() {
        return Ok(ConfidentialSpacePolicy::new_unendorsed(root_certificate));
    }

    let cosign_reference_values = CosignReferenceValues::from_proto(
        &reference_values.cosign_reference_values.clone().unwrap_or_default(),
    )
    .map_err(anyhow::Error::msg)?;

    Ok(ConfidentialSpacePolicy::new(root_certificate, cosign_reference_values))
}

#[cfg(test)]
mod tests {
    use oak_file_utils::read_testdata_string;
    use oak_proto_rust::oak::attestation::v1::{
        ConfidentialSpaceReferenceValues, CosignReferenceValues as CosignReferenceValuesProto,
    };
    use oak_proto_rust_lib::p256_ecdsa_verifying_key_to_proto;
    use p256::pkcs8::DecodePublicKey;

    use super::*;

    #[test]
    fn confidential_space_complete_policy_generated() {
        let root_certificate_pem = read_testdata_string!("root_ca_cert.pem");
        let developer_public_key_pem = read_testdata_string!("developer_key.pub.pem");
        let developer_public_key =
            p256::ecdsa::VerifyingKey::from_public_key_pem(&developer_public_key_pem).unwrap();

        let reference_values = ConfidentialSpaceReferenceValues {
            root_certificate_pem,
            cosign_reference_values: Some(CosignReferenceValuesProto {
                developer_public_key: Some(p256_ecdsa_verifying_key_to_proto(
                    &developer_public_key,
                )),
                ..Default::default()
            }),
        };

        let policy = confidential_space_policy_from_reference_values(&reference_values);

        assert!(policy.is_ok(), "Failed: {:?}", policy.err().unwrap());
    }

    #[test]
    fn confidential_space_policy_no_cosign_reference_values() {
        let root_certificate_pem = read_testdata_string!("root_ca_cert.pem");

        let reference_values = ConfidentialSpaceReferenceValues {
            root_certificate_pem,
            cosign_reference_values: None,
        };

        let policy = confidential_space_policy_from_reference_values(&reference_values);
        assert!(policy.is_ok(), "Failed: {:?}", policy.err().unwrap());
    }

    #[test]
    fn confidential_space_policy_no_root_certificate() {
        let developer_public_key_pem = read_testdata_string!("developer_key.pub.pem");
        let developer_public_key =
            p256::ecdsa::VerifyingKey::from_public_key_pem(&developer_public_key_pem).unwrap();

        let reference_values = ConfidentialSpaceReferenceValues {
            root_certificate_pem: "".to_string(),
            cosign_reference_values: Some(CosignReferenceValuesProto {
                developer_public_key: Some(p256_ecdsa_verifying_key_to_proto(
                    &developer_public_key,
                )),
                ..Default::default()
            }),
        };

        let policy = confidential_space_policy_from_reference_values(&reference_values);
        assert!(policy.is_err(), "Policy succeeded when it should have failed");
    }
}
