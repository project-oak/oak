//
// Copyright 2023 The Project Oak Authors
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

use crate::{
    attester::{Attester, EmptyAttestationReportGenerator},
    verifier::{AttestationVerifier, InsecureAttestationVerifier, ReferenceValue},
    proto::oak::session::v1::AttestationEndorsement,
};
use oak_crypto::{
    encryptor::EncryptionKeyProvider,
};
use alloc::{vec, sync::Arc};

const TEST_ATTESTATION_ENDORSEMENT: AttestationEndorsement = AttestationEndorsement {
    tee_certificates: vec![],
    binary_attestation: None,
    application_data: None,
};
const TEST_REFERENCE_VALUE: ReferenceValue = ReferenceValue { binary_hash: vec![] };

#[test]
fn test_empty_attestation() {
    let attestation_report_generator = Arc::new(EmptyAttestationReportGenerator);
    let encryption_key_provider = Arc::new(EncryptionKeyProvider::new());
    let attester = Arc::new(Attester::new(attestation_report_generator, encryption_key_provider));
    let attestation_evidence = attester.generate_attestation_evidence().expect("couldn't generate attestation evidence");

    let verify_result = InsecureAttestationVerifier::verify(
        &attestation_evidence,
        &TEST_ATTESTATION_ENDORSEMENT,
        &TEST_REFERENCE_VALUE,
    );
    assert!(verify_result.is_ok());
}
