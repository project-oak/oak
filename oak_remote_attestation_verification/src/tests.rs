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
use alloc::{sync::Arc, vec, vec::Vec};
use base64::{prelude::BASE64_STANDARD, Engine as _};
use oak_crypto::encryptor::EncryptionKeyProvider;
use oak_remote_attestation::{
    attester::{Attester, EmptyAttestationReportGenerator},
    proto::oak::session::v1::{AttestationEndorsement, BinaryAttestation},
};

use crate::proto::oak::verification::v1::{
    transparency_verification_options::RekorEntryVerification::{self, VerificationData},
    SkipRekorEntryVerification, TransparencyVerificationOptions,
};

use crate::verifier::{
    verify_transparent_release_endorsement, AttestationVerifier, InsecureAttestationVerifier,
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

const BINARY_DIGEST: &str = "39051983bbb600bbfb91bd22ee4c976420f8f0c6a895fd083dcb0d153ddd5fd6";

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
    let attestation_report_generator = Arc::new(EmptyAttestationReportGenerator);
    let encryption_key_provider = Arc::new(EncryptionKeyProvider::new());
    let attester = Arc::new(Attester::new(
        attestation_report_generator,
        encryption_key_provider,
    ));
    let attestation_evidence = attester
        .generate_attestation_evidence()
        .expect("couldn't generate attestation evidence");

    let verify_result = InsecureAttestationVerifier::verify(
        &attestation_evidence,
        &TEST_ATTESTATION_ENDORSEMENT,
        &TEST_REFERENCE_VALUE,
    );
    assert!(verify_result.is_ok());
}

#[test]
fn test_verify_transparent_release_endorsement_with_rekor_verification() {
    let testdata = load_testdata();
    let skip_rekor_verification = false;
    let verification_options = get_verification_options(&testdata, skip_rekor_verification);

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement_bytes,
        rekor_log_entry: testdata.log_entry_bytes,
        base64_pem_encoded_rekor_public_key: BASE64_STANDARD
            .encode(&testdata.rekor_public_key_pem_bytes),
    };

    let result = verify_transparent_release_endorsement(
        BINARY_DIGEST.as_bytes(),
        "sha256",
        &binary_attestation,
        &verification_options,
    );
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_transparent_release_endorsement_with_rekor_verification_but_missing_digest() {
    let testdata = load_testdata();
    let skip_rekor_verification = false;
    let verification_options = get_verification_options(&testdata, skip_rekor_verification);

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement_bytes,
        rekor_log_entry: testdata.log_entry_bytes,
        base64_pem_encoded_rekor_public_key: BASE64_STANDARD
            .encode(&testdata.rekor_public_key_pem_bytes),
    };

    let result = verify_transparent_release_endorsement(
        BINARY_DIGEST.as_bytes(),
        "sha2-384",
        &binary_attestation,
        &verification_options,
    );
    assert!(result.is_err(), "{:?}", result);
    assert!(result
        .map_err(|err| format!("{err}"))
        .unwrap_err()
        .contains("missing sha2-384 digest"));
}

#[test]
fn test_verify_transparent_release_endorsement_with_rekor_verification_but_invalid_rekor_public_key(
) {
    let testdata = load_testdata();
    let skip_rekor_verification = false;
    let verification_options = get_verification_options(&testdata, skip_rekor_verification);

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement_bytes,
        rekor_log_entry: testdata.log_entry_bytes,
        base64_pem_encoded_rekor_public_key: BASE64_STANDARD
            .encode(&testdata.endorser_public_key_pem_bytes),
    };

    let result = verify_transparent_release_endorsement(
        BINARY_DIGEST.as_bytes(),
        "sha256",
        &binary_attestation,
        &verification_options,
    );
    assert!(result.is_err(), "{:?}", result);
    assert!(result
        .map_err(|err| format!("{err}"))
        .unwrap_err()
        .contains("Rekor public key verification failed"));
}

#[test]
fn test_verify_transparent_release_endorsement_no_rekor_entry_and_skip_rekor_verification() {
    let testdata = load_testdata();
    let skip_rekor_verification = true;
    let verification_options = get_verification_options(&testdata, skip_rekor_verification);

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement_bytes,
        rekor_log_entry: Vec::new(),
        base64_pem_encoded_rekor_public_key: "".to_string(),
    };

    let result = verify_transparent_release_endorsement(
        BINARY_DIGEST.as_bytes(),
        "sha256",
        &binary_attestation,
        &verification_options,
    );
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_transparent_release_endorsement_no_rekor_entry_but_require_rekor_verification() {
    let testdata = load_testdata();
    let skip_rekor_verification = false;
    let verification_options = get_verification_options(&testdata, skip_rekor_verification);

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement_bytes,
        rekor_log_entry: Vec::new(),
        base64_pem_encoded_rekor_public_key: "".to_string(),
    };

    let result = verify_transparent_release_endorsement(
        BINARY_DIGEST.as_bytes(),
        "sha256",
        &binary_attestation,
        &verification_options,
    );
    assert!(result.is_err(), "{:?}", result);
}

fn get_verification_options(
    testdata: &TestData,
    skip_rekor_verification: bool,
) -> TransparencyVerificationOptions {
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

    TransparencyVerificationOptions {
        rekor_entry_verification,
    }
}
