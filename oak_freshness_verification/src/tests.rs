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

use alloc::string::ToString;
use core::assert_matches::assert_matches;

use mockall::*;
use nist_pulse_verifier::__mock_MockApiGetter_ApiGetter::__get::Expectation;
use oak_proto_rust::oak::crypto::v1::ProofOfFreshness;

use crate::nist_pulse_verifier::{
    self, MockApiGetter, NistPulseVerifier, ProofOfFreshnessVerificationError,
};

const MOCK_CERTIFICATE_RESPONSE_STRING: &str = include_str!("testdata/certificate.pem");

const MOCK_JSON_RESPONSE_STRING: &str = r#"{
        "pulse": {
            "uri": "https://beacon.nist.gov/beacon/2.0/chain/2/pulse/1352280",
            "version": "Version 2.0",
            "cipherSuite": 0,
            "period": 60000,
            "certificateId": "some-cert-id",
            "chainIndex": 2,
            "pulseIndex": 1352280,
            "timeStamp": "2025-07-30T00:00:00.000Z",
            "localRandomValue": "some-random-value",
            "external": {
                "sourceId": "some-source-id",
                "statusCode": 0,
                "value": "some-value"
            },
            "listValues": [],
            "precommitmentValue": "some-precommitment-value",
            "statusCode": 0,
            "signatureValue": "some-signature",
            "outputValue": "B097474508DA9EEFEA3DC10F882F9262C6F2D3D9F428FCF981BB67271DA57606226E1E138EDD481712F6DBAF6BCA1B3E0E55FB3F2011EC4FFFBAD5A5635E722E"
        }
    }"#;

const DEFAULT_PULSE_URL: &str = "https://beacon.nist.gov/beacon/2.0/chain/2/pulse/1352280";
const DEFAULT_CERTIFICATE_URL: &str = "https://beacon.nist.gov/beacon/2.0/certificate/some-cert-id";

// Modifies the mock api getter to expect a single get call to the url.
fn expect_get_once<'a>(
    mock_getter: &'a mut MockApiGetter,
    url: &'static str,
) -> &'a mut Expectation {
    mock_getter.expect_get().with(predicate::eq(url)).once()
}

#[test]
fn verify_nist_pulse_successful() {
    let mut mock_getter = MockApiGetter::new();
    expect_get_once(&mut mock_getter, DEFAULT_PULSE_URL)
        .returning(move |_| Ok(MOCK_JSON_RESPONSE_STRING.to_string()));
    expect_get_once(&mut mock_getter, DEFAULT_CERTIFICATE_URL)
        .returning(move |_| Ok(MOCK_CERTIFICATE_RESPONSE_STRING.to_string()));

    let verifier = NistPulseVerifier::new(Box::new(mock_getter));
    let nist_pulse = ProofOfFreshness {
        nist_chain_index: 2,
        nist_pulse_index: 1352280,
        nist_pulse_output_value: hex::decode("B097474508DA9EEFEA3DC10F882F9262C6F2D3D9F428FCF981BB67271DA57606226E1E138EDD481712F6DBAF6BCA1B3E0E55FB3F2011EC4FFFBAD5A5635E722E")
            .unwrap(),
    };
    assert_matches!(
        verifier.verify(nist_pulse),
        Err(ProofOfFreshnessVerificationError::SignatureVerificationNotImplemented)
    );
}

#[test]
fn verify_nist_pulse_mismatch_output_value() {
    let mut mock_getter = MockApiGetter::new();
    expect_get_once(&mut mock_getter, DEFAULT_PULSE_URL)
        .returning(move |_| Ok(MOCK_JSON_RESPONSE_STRING.to_string()));

    let verifier = NistPulseVerifier::new(Box::new(mock_getter));
    let incorrect_pulse_output_value = "7435D447C495ECB94CDF749F87EFFC758FEFF18020E4DBACC5D5BB5A6D0AD8338D049A04B3B51B9D5CE9E9E7454427210AB3252D5AF38142B5A374E6BDC8E616";
    let invalid_nist_pulse = ProofOfFreshness {
        nist_chain_index: 2,
        nist_pulse_index: 1352280,
        nist_pulse_output_value: hex::decode(incorrect_pulse_output_value).unwrap(),
    };

    let result = verifier.verify(invalid_nist_pulse);
    assert_matches!(result, Err(ProofOfFreshnessVerificationError::OutputValueNotFound { .. }));

    // Ensure OutputValueNotFound error is structured as expected. Since
    // ProofOfFreshnessVerificationError does not derive PartialEq (this stems from
    // the arguement errors such as serde_json::Error not deriving PartialEq), we
    // compare the strings.
    let actual_pulse_output_value = "B097474508DA9EEFEA3DC10F882F9262C6F2D3D9F428FCF981BB67271DA57606226E1E138EDD481712F6DBAF6BCA1B3E0E55FB3F2011EC4FFFBAD5A5635E722E";
    let expected_error = ProofOfFreshnessVerificationError::OutputValueNotFound {
        expected: incorrect_pulse_output_value.to_string(),
        actual: actual_pulse_output_value.to_string(),
    };
    assert_eq!(result.unwrap_err().to_string(), expected_error.to_string());
}

#[test]
fn verify_nist_pulse_invalid_hexadecimal() {
    let mut mock_getter = MockApiGetter::new();
    let invalid_hex_response = MOCK_JSON_RESPONSE_STRING.replace(
        "B097474508DA9EEFEA3DC10F882F9262C6F2D3D9F428FCF981BB67271DA57606226E1E138EDD481712F6DBAF6BCA1B3E0E55FB3F2011EC4FFFBAD5A5635E722E",
        "invalid-hex",
    );
    expect_get_once(&mut mock_getter, DEFAULT_PULSE_URL)
        .returning(move |_| Ok(invalid_hex_response.clone()));

    let verifier = NistPulseVerifier::new(Box::new(mock_getter));
    let nist_pulse_with_invalid_hex = ProofOfFreshness {
        nist_chain_index: 2,
        nist_pulse_index: 1352280,
        nist_pulse_output_value: b"some-output-value".to_vec(),
    };
    assert_matches!(
        verifier.verify(nist_pulse_with_invalid_hex),
        Err(ProofOfFreshnessVerificationError::InvalidHexadecimal(_))
    );
}

#[test]
fn verify_nist_pulse_api_call_failed() {
    let mut mock_getter = MockApiGetter::new();
    expect_get_once(&mut mock_getter, DEFAULT_PULSE_URL)
        .returning(|_| Err("API call failed".into()));

    let verifier = NistPulseVerifier::new(Box::new(mock_getter));
    let nist_pulse = ProofOfFreshness {
        nist_chain_index: 2,
        nist_pulse_index: 1352280,
        nist_pulse_output_value: b"some-output-value".to_vec(),
    };
    assert_matches!(
        verifier.verify(nist_pulse),
        Err(ProofOfFreshnessVerificationError::ApiCallFailed(_))
    );
}

#[test]
fn verify_nist_pulse_json_parsing_failed() {
    let mut mock_getter = MockApiGetter::new();
    expect_get_once(&mut mock_getter, DEFAULT_PULSE_URL)
        .returning(|_| Ok("invalid-json".to_string()));

    let verifier = NistPulseVerifier::new(Box::new(mock_getter));
    let nist_pulse = ProofOfFreshness {
        nist_chain_index: 2,
        nist_pulse_index: 1352280,
        nist_pulse_output_value: b"some-output-value".to_vec(),
    };
    assert_matches!(
        verifier.verify(nist_pulse),
        Err(ProofOfFreshnessVerificationError::JsonParsingFailed(_))
    );
}

#[test]
fn verify_nist_pulse_json_certificate_parsing_failed() {
    let mut mock_getter = MockApiGetter::new();
    expect_get_once(&mut mock_getter, DEFAULT_PULSE_URL)
        .returning(|_| Ok(MOCK_JSON_RESPONSE_STRING.to_string()));
    expect_get_once(&mut mock_getter, DEFAULT_CERTIFICATE_URL)
        .returning(|_| Ok("invalid certificate".to_string()));

    let verifier = NistPulseVerifier::new(Box::new(mock_getter));
    let nist_pulse = ProofOfFreshness {
        nist_chain_index: 2,
        nist_pulse_index: 1352280,
        nist_pulse_output_value: hex::decode("B097474508DA9EEFEA3DC10F882F9262C6F2D3D9F428FCF981BB67271DA57606226E1E138EDD481712F6DBAF6BCA1B3E0E55FB3F2011EC4FFFBAD5A5635E722E")
            .unwrap(),
    };

    assert_matches!(
        verifier.verify(nist_pulse),
        Err(ProofOfFreshnessVerificationError::CertificateParsingFailed { .. })
    );
}
