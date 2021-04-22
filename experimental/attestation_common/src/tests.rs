//
// Copyright 2021 The Project Oak Authors
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

use crate::report::{AttestationInfo, Report};
use assert_matches::assert_matches;

const TEST_TEE_DATA: &str = "Data";
const TEST_CERTIFICATE: &str = "Certificate";
const TEST_ATTESTATION_INFO: &str = r#"{"report":{"version":0,"svn":0,"platform_version":0,"data":[68,97,116,97],"measurement":[84,101,115,116,32,84,69,69,32,109,101,97,115,117,114,101,109,101,110,116],"signature":[]},"certificate":[67,101,114,116,105,102,105,99,97,116,101]}"#;

#[test]
fn test_attestation_info_serialization() {
    let attestation_info = AttestationInfo {
        report: Report::new(TEST_TEE_DATA.as_bytes()),
        certificate: TEST_CERTIFICATE.as_bytes().to_vec(),
    };

    let serialized_attestation_info_result = attestation_info.to_string();
    assert_matches!(serialized_attestation_info_result, Ok(_));
    let serialized_attestation_info = serialized_attestation_info_result.unwrap();
    assert_eq!(serialized_attestation_info, TEST_ATTESTATION_INFO);

    let deserialized_attestation_info_result = AttestationInfo::from_string(TEST_ATTESTATION_INFO);
    assert_matches!(deserialized_attestation_info_result, Ok(_));
    let deserialized_attestation_info = deserialized_attestation_info_result.unwrap();
    assert_eq!(deserialized_attestation_info, attestation_info);
}
