//
// Copyright 2022 The Project Oak Authors
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

use crate::rekor::*;
use std::fs;

use crate::proto::oak::verification::v1::RekorEntryVerificationData;
use alloc::{collections::BTreeMap, sync::Arc, vec, vec::Vec};
use base64::{prelude::BASE64_STANDARD, Engine as _};
use oak_crypto::encryptor::EncryptionKeyProvider;
use oak_remote_attestation::{
    attester::{Attester, EmptyAttestationReportGenerator},
    proto::oak::session::v1::{AttestationEndorsement, AttestationEvidence, BinaryAttestation},
};

use crate::proto::oak::verification::v1::{
    transparency_verification_options::RekorEntryVerification::{self, VerificationData},
    AttestationVerificationOptions, LayerVerificationOptions, SkipRekorEntryVerification,
    TransparencyVerificationOptions,
};

use crate::verifier::{
    AttestationVerifier, ConfigurableAttestationVerifier, InsecureAttestationVerifier,
    ReferenceValue,
};

const TEST_ATTESTATION_ENDORSEMENT: AttestationEndorsement = AttestationEndorsement {
    tee_certificates: vec![],
    binary_attestation: None,
    application_data: None,
};
const TEST_REFERENCE_VALUE: ReferenceValue = ReferenceValue {
    binary_hash: vec![],
};

struct TestData {
    endorsement_bytes: Vec<u8>,
    log_entry_bytes: Vec<u8>,
    rekor_public_key_pem_bytes: Vec<u8>,
    endorser_public_key_pem_bytes: Vec<u8>,
}

fn load_testdata() -> TestData {
    let endorsement_path = "testdata/endorsement.json";

    // LogEntry downloaded from
    // https://rekor.sigstore.dev/api/v1/log/entries/24296fb24b8ad77a51d549703a3a1c2dd2639ba49617fc563854031cb93e6d354e7b005065c334a8.
    // This LogEntry was created by signing the example endorsement file above, using google-cloud
    // KMS, and uploading it to Rekor (https://rekor.sigstore.dev) using `rekor-cli`, as described
    // in https://github.com/sigstore/rekor/blob/main/types.md#pkixx509.
    // The resulting entry in Rekor has UUID
    // `24296fb24b8ad77a51d549703a3a1c2dd2639ba49617fc563854031cb93e6d354e7b005065c334a8` and
    // logIndex 30891523. The body of LogEntry can be fetched using `rekor-cli get --log-index
    // 30891523`.
    let log_entry_path = "testdata/logentry.json";

    // Public key fetched from Google Cloud KMS, associated with the signing key that was used for
    // signing the endorsement statement.
    let pubkey_path = "testdata/oak-development.pem";

    // Public key of the Rekor instance hosted by sigstore.dev. It is downloaded from
    // https://rekor.sigstore.dev/api/v1/log/publicKey.
    let rekor_pubkey_path = "testdata/rekor_public_key.pem";

    let endorsement_bytes = fs::read(endorsement_path).expect("couldn't read endorsement file");
    let log_entry_bytes = fs::read(log_entry_path).expect("couldn't read log entry file");
    let rekor_public_key_pem_bytes =
        fs::read(rekor_pubkey_path).expect("couldn't read Rekor's public key file");
    let endorser_public_key_pem_bytes =
        fs::read(pubkey_path).expect("couldn't read product team's public key file");

    TestData {
        endorsement_bytes,
        log_entry_bytes,
        rekor_public_key_pem_bytes,
        endorser_public_key_pem_bytes,
    }
}

#[test]
fn test_verify_rekor_log_entry() {
    let testdata = load_testdata();

    let result = verify_rekor_log_entry(
        &testdata.log_entry_bytes,
        &testdata.rekor_public_key_pem_bytes,
        &testdata.endorsement_bytes,
    );
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_unmarshal_pem_public_key() {
    let pubkey_path = "testdata/rekor_public_key.pem";
    let pem_bytes = fs::read(pubkey_path).expect("couldn't read Rekor's public key file");

    let key = unmarshal_pem_to_p256_public_key(&pem_bytes);
    assert!(key.is_ok());
}

#[test]
fn test_verify_rekor_signature() {
    let entry_path = "testdata/logentry.json";
    let pubkey_path = "testdata/rekor_public_key.pem";

    let log_entry_bytes = fs::read(entry_path).expect("couldn't read Rekor log entry");
    let pem_bytes = fs::read(pubkey_path).expect("couldn't read Rekor's public key file");

    let result = verify_rekor_signature(&log_entry_bytes, &pem_bytes);

    assert!(result.is_ok());
}

#[test]
fn test_empty_attestation() {
    let attestation_evidence = generate_empty_attestation_evidence();

    let verify_result = InsecureAttestationVerifier {}.verify(
        &attestation_evidence,
        &TEST_ATTESTATION_ENDORSEMENT,
        &TEST_REFERENCE_VALUE,
    );
    assert!(verify_result.is_ok());
}

#[test]
fn test_configurable_attestation_verifier() {
    let testdata = load_testdata();
    let verifier =
        ConfigurableAttestationVerifier::create(&get_verification_options(&testdata, false));

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement_bytes,
        rekor_log_entry: testdata.log_entry_bytes,
        base64_pem_encoded_rekor_public_key: BASE64_STANDARD
            .encode(&testdata.rekor_public_key_pem_bytes),
    };

    let attestation_evidence = generate_empty_attestation_evidence();
    let attestation_endorsement = AttestationEndorsement {
        tee_certificates: vec![],
        binary_attestation: Some(binary_attestation),
        application_data: None,
    };

    let result = verifier.verify(
        &attestation_evidence,
        &attestation_endorsement,
        &TEST_REFERENCE_VALUE,
    );
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_configurable_attestation_verifier_no_rekor_entry_and_skip_rekor_verification() {
    let testdata = load_testdata();
    let verifier =
        ConfigurableAttestationVerifier::create(&get_verification_options(&testdata, true));

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement_bytes,
        rekor_log_entry: Vec::new(),
        base64_pem_encoded_rekor_public_key: "".to_string(),
    };

    let attestation_evidence = generate_empty_attestation_evidence();
    let attestation_endorsement = AttestationEndorsement {
        tee_certificates: vec![],
        binary_attestation: Some(binary_attestation),
        application_data: None,
    };

    let result = verifier.verify(
        &attestation_evidence,
        &attestation_endorsement,
        &TEST_REFERENCE_VALUE,
    );
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_configurable_attestation_verifier_no_rekor_entry_and_require_rekor_verification() {
    let testdata = load_testdata();
    let verifier =
        ConfigurableAttestationVerifier::create(&get_verification_options(&testdata, false));

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement_bytes,
        rekor_log_entry: Vec::new(),
        base64_pem_encoded_rekor_public_key: "".to_string(),
    };

    let attestation_evidence = generate_empty_attestation_evidence();
    let attestation_endorsement = AttestationEndorsement {
        tee_certificates: vec![],
        binary_attestation: Some(binary_attestation),
        application_data: None,
    };

    let result = verifier.verify(
        &attestation_evidence,
        &attestation_endorsement,
        &TEST_REFERENCE_VALUE,
    );
    assert!(result.is_err(), "{:?}", result);
}

fn get_verification_options(
    testdata: &TestData,
    skip_rekor_verification: bool,
) -> AttestationVerificationOptions {
    let base64_pem_encoded_rekor_public_key =
        BASE64_STANDARD.encode(&testdata.rekor_public_key_pem_bytes);
    let base64_pem_encoded_endorser_public_key =
        BASE64_STANDARD.encode(&testdata.endorser_public_key_pem_bytes);

    let rekor_entry_verification = match skip_rekor_verification {
        true => Some(RekorEntryVerification::Skip(SkipRekorEntryVerification {})),
        false => Some(VerificationData(RekorEntryVerificationData {
            base64_pem_encoded_rekor_public_key,
            base64_pem_encoded_endorser_public_key,
        })),
    };

    let default_transparency_verification_options = Some(TransparencyVerificationOptions {
        rekor_entry_verification,
    });
    let default_layer_verification_option = Some(LayerVerificationOptions {
        transparency_verification_options: BTreeMap::new(),
        default_transparency_verification_options,
        reference_value_verification_options: None,
    });

    AttestationVerificationOptions {
        supported_tee_platforms: Vec::new(),
        skip_tee_certificate_verification: true,
        layer_verification_options: BTreeMap::new(),
        default_layer_verification_option,
    }
}

fn generate_empty_attestation_evidence() -> AttestationEvidence {
    let attestation_report_generator = Arc::new(EmptyAttestationReportGenerator);
    let encryption_key_provider = Arc::new(EncryptionKeyProvider::new());
    let attester = Arc::new(Attester::new(
        attestation_report_generator,
        encryption_key_provider,
    ));

    attester
        .generate_attestation_evidence()
        .expect("couldn't generate attestation evidence")
}
