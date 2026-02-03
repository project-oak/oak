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

use anyhow::Result;
use oak_attestation_verification::{create_amd_verifier, create_insecure_verifier};
use oak_attestation_verification_types::assertion_verifier::AssertionVerifier;
use oak_file_utils::data_path;
use oak_proto_rust::oak::attestation::v1::{
    Assertion, EndorsedEvidenceAssertion, Endorsements, Evidence, ReferenceValues,
};
use oak_time::{Instant, clock::FixedClock};
use prost::Message;
use test_util::AttestationData;

use crate::{
    assertion_verifier::EndorsedEvidenceAssertionVerifier,
    key_extractor::EventLogSigningKeyExtractor,
};

#[test]
fn verify_succeeds() -> Result<()> {
    let clock = FixedClock::at_instant(Instant::UNIX_EPOCH);
    let attestation_verifier =
        Box::new(create_insecure_verifier(clock, &load_reference_values()?).expect("no verifier"));
    let assertion_verifier = EndorsedEvidenceAssertionVerifier {
        attestation_verifier,
        key_extractor: Box::new(EventLogSigningKeyExtractor {}),
    };
    let endorsed_evidence_assertion = EndorsedEvidenceAssertion {
        evidence: Some(load_evidence()?),
        endorsements: Some(load_endorsements()?),
        asserted_data_signature: load_asserted_data_signature()?,
    };
    let assertion = Assertion { content: endorsed_evidence_assertion.encode_to_vec() };

    assert!(
        assertion_verifier.verify(&assertion, &load_asserted_data()?, Instant::UNIX_EPOCH).is_ok()
    );
    Ok(())
}

#[test]
fn verify_signature_mismatch_fails() -> Result<()> {
    let clock = FixedClock::at_instant(Instant::UNIX_EPOCH);
    let attestation_verifier =
        Box::new(create_insecure_verifier(clock, &load_reference_values()?).expect("no verifier"));
    let assertion_verifier = EndorsedEvidenceAssertionVerifier {
        attestation_verifier,
        key_extractor: Box::new(EventLogSigningKeyExtractor {}),
    };
    let mut corrupted_signature = load_asserted_data_signature()?;
    corrupted_signature.reverse();
    let endorsed_evidence_assertion = EndorsedEvidenceAssertion {
        evidence: Some(load_evidence()?),
        endorsements: Some(load_endorsements()?),
        asserted_data_signature: corrupted_signature,
    };
    let assertion = Assertion { content: endorsed_evidence_assertion.encode_to_vec() };

    assert!(
        assertion_verifier.verify(&assertion, &load_asserted_data()?, Instant::UNIX_EPOCH).is_err()
    );
    Ok(())
}

#[test]
fn verify_failed_attestation_fails() -> Result<()> {
    let clock = FixedClock::at_instant(Instant::UNIX_EPOCH);
    // Our test evidence is not hardware rooted so AMD verifier will fail
    let attestation_verifier = Box::new(
        create_amd_verifier(clock, &AttestationData::load_milan_oc_release().reference_values)
            .expect("no verifier"),
    );
    let assertion_verifier = EndorsedEvidenceAssertionVerifier {
        attestation_verifier,
        key_extractor: Box::new(EventLogSigningKeyExtractor {}),
    };
    let endorsed_evidence_assertion = EndorsedEvidenceAssertion {
        evidence: Some(load_evidence()?),
        endorsements: Some(load_endorsements()?),
        asserted_data_signature: load_asserted_data_signature()?,
    };
    let assertion = Assertion { content: endorsed_evidence_assertion.encode_to_vec() };

    assert!(
        assertion_verifier.verify(&assertion, &load_asserted_data()?, Instant::UNIX_EPOCH).is_err()
    );
    Ok(())
}

fn load_reference_values() -> Result<ReferenceValues> {
    let bytes = std::fs::read(data_path(
        "oak_attestation_verification/endorsed_evidence/testdata/reference_values.binarypb",
    ))?;
    Ok(ReferenceValues::decode(bytes.as_slice())?)
}

fn load_endorsements() -> Result<Endorsements> {
    let bytes = std::fs::read(data_path(
        "oak_attestation_verification/endorsed_evidence/testdata/endorsements.binarypb",
    ))?;
    Ok(Endorsements::decode(bytes.as_slice())?)
}

fn load_evidence() -> Result<Evidence> {
    let bytes = std::fs::read(data_path(
        "oak_attestation_verification/endorsed_evidence/testdata/evidence.binarypb",
    ))?;
    Ok(Evidence::decode(bytes.as_slice())?)
}

fn load_asserted_data() -> Result<Vec<u8>> {
    Ok(std::fs::read(data_path(
        "oak_attestation_verification/endorsed_evidence/testdata/asserted_data",
    ))?)
}

fn load_asserted_data_signature() -> Result<Vec<u8>> {
    Ok(std::fs::read(data_path(
        "oak_attestation_verification/endorsed_evidence/testdata/asserted_data_signature",
    ))?)
}
