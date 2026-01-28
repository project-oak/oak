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

use oak_proto_rust::oak::attestation::v1::{
    binary_reference_value, confidential_space_reference_values, BinaryReferenceValue,
    ConfidentialSpaceReferenceValues,
};
use verify_endorsement::create_endorsement_reference_value;
use x509_cert::{der::DecodePem, Certificate};

use crate::policy::{ConfidentialSpacePolicy, WorkloadReferenceValues};

// Allways generates a policy that verifies whether the workload is running on
// Confidential Space. By extension, `root_certificate_pem` must always be
// specified.
pub fn confidential_space_policy_from_reference_values(
    reference_values: &ConfidentialSpaceReferenceValues,
) -> anyhow::Result<ConfidentialSpacePolicy> {
    let root_certificate = Certificate::from_pem(&reference_values.root_certificate_pem)
        .map_err(anyhow::Error::msg)?;

    match &reference_values.r#container_image {
        #[allow(deprecated)]
        Some(confidential_space_reference_values::ContainerImage::CosignReferenceValues(
            cosign_reference_values,
        )) => {
            let endorser_key = cosign_reference_values
                .developer_public_key
                .as_ref()
                .ok_or(anyhow::anyhow!("endorser public key missing"))?
                .clone();
            let rekor_key = cosign_reference_values.rekor_public_key.clone();
            let ref_value = create_endorsement_reference_value(endorser_key, rekor_key);
            let binary_ref_value = BinaryReferenceValue {
                r#type: Some(binary_reference_value::Type::Endorsement(ref_value)),
            };
            let workload_ref_values =
                WorkloadReferenceValues::ImageReferenceValue(binary_ref_value);
            Ok(ConfidentialSpacePolicy::new(root_certificate, workload_ref_values))
        }
        Some(
            confidential_space_reference_values::ContainerImage::ContainerImageReferencePrefix(
                container_image_reference_prefix,
            ),
        ) => {
            let workload_ref_values = WorkloadReferenceValues::ContainerImageReferencePrefix(
                container_image_reference_prefix.clone(),
            );
            Ok(ConfidentialSpacePolicy::new(root_certificate, workload_ref_values))
        }
        Some(confidential_space_reference_values::ContainerImage::ImageReferenceValue(
            ref_value,
        )) => {
            let workload_ref_values =
                WorkloadReferenceValues::ImageReferenceValue(ref_value.clone());
            Ok(ConfidentialSpacePolicy::new(root_certificate, workload_ref_values))
        }
        None => Ok(ConfidentialSpacePolicy::new_unendorsed(root_certificate)),
    }
}

#[cfg(test)]
mod tests {
    use oak_file_utils::read_testdata_string;
    use oak_proto_rust::oak::attestation::v1::{
        confidential_space_reference_values, ConfidentialSpaceReferenceValues,
        CosignReferenceValues as CosignReferenceValuesProto,
    };
    use verify_endorsement::create_verifying_key_from_pem;

    use super::*;

    #[test]
    fn confidential_space_policy_generated_with_cosign_succeeds() {
        let root_certificate_pem = read_testdata_string!("root_ca_cert.pem");
        let developer_public_key_pem = read_testdata_string!("developer_key.pub.pem");
        let developer_key = create_verifying_key_from_pem(&developer_public_key_pem, 0);

        let reference_values = ConfidentialSpaceReferenceValues {
            root_certificate_pem,
            r#container_image: Some(
                #[allow(deprecated)]
                confidential_space_reference_values::ContainerImage::CosignReferenceValues(
                    CosignReferenceValuesProto {
                        developer_public_key: Some(developer_key),
                        ..Default::default()
                    },
                ),
            ),
        };

        let policy = confidential_space_policy_from_reference_values(&reference_values);

        assert!(policy.is_ok(), "Failed: {:?}", policy.err().unwrap());
    }

    #[test]
    fn confidential_space_policy_generated_with_container_image_reference_succeeds() {
        let root_certificate_pem = read_testdata_string!("root_ca_cert.pem");
        let container_image_reference_prefix =
            "europe-west2-docker.pkg.dev/oak-ci/example-enclave-apps/echo_enclave_app";

        let reference_values = ConfidentialSpaceReferenceValues {
            root_certificate_pem,
            r#container_image: Some(
                confidential_space_reference_values::ContainerImage::ContainerImageReferencePrefix(
                    container_image_reference_prefix.to_string(),
                ),
            ),
        };

        let policy = confidential_space_policy_from_reference_values(&reference_values);

        assert!(policy.is_ok(), "Failed: {:?}", policy.err().unwrap());
    }

    #[test]
    fn confidential_space_policy_no_workload_reference_values_succeeds() {
        let root_certificate_pem = read_testdata_string!("root_ca_cert.pem");

        let reference_values =
            ConfidentialSpaceReferenceValues { root_certificate_pem, r#container_image: None };

        let policy = confidential_space_policy_from_reference_values(&reference_values);
        assert!(policy.is_ok(), "Failed: {:?}", policy.err().unwrap());
    }

    #[test]
    fn confidential_space_policy_no_root_certificate_fails() {
        let developer_public_key_pem = read_testdata_string!("developer_key.pub.pem");
        let developer_key = create_verifying_key_from_pem(&developer_public_key_pem, 0);

        let reference_values = ConfidentialSpaceReferenceValues {
            root_certificate_pem: "".to_string(),
            #[allow(deprecated)]
            r#container_image: Some(
                confidential_space_reference_values::ContainerImage::CosignReferenceValues(
                    CosignReferenceValuesProto {
                        developer_public_key: Some(developer_key),
                        ..Default::default()
                    },
                ),
            ),
        };

        let policy = confidential_space_policy_from_reference_values(&reference_values);
        assert!(policy.is_err(), "Policy succeeded when it should have failed");
    }
}
