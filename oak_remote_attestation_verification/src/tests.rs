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

use crate::{rekor::*, verifier::*};
use std::fs;

use alloc::{sync::Arc, vec, vec::Vec};
use base64::{prelude::BASE64_STANDARD, Engine as _};
use oak_crypto::encryptor::EncryptionKeyProvider;
use oak_remote_attestation::{
    attester::{Attester, EmptyAttestationReportGenerator},
    proto::oak::session::v1::{AttestationEndorsement, BinaryAttestation},
};

use crate::verifier::{
    convert_pem_to_raw, convert_raw_to_pem, verify_binary_endorsement, AttestationVerifier,
    InsecureAttestationVerifier, ReferenceValue,
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

const ENDORSEMENT_PATH: &str = "testdata/endorsement.json";
const ENDORSEMENT_SIGNATURE_PATH: &str = "testdata/endorsement.json.sig";

// Public key fetched from Google Cloud KMS, associated with the signing key that was used for
// signing the endorsement statement.
const ENDORSER_PUBLIC_KEY_PATH: &str = "testdata/oak-development.pem";

// LogEntry downloaded from
// https://rekor.sigstore.dev/api/v1/log/entries/24296fb24b8ad77a51d549703a3a1c2dd2639ba49617fc563854031cb93e6d354e7b005065c334a8.
// This LogEntry was created by signing the example endorsement file above, using google-cloud
// KMS, and uploading it to Rekor (https://rekor.sigstore.dev) using `rekor-cli`, as described
// in https://github.com/sigstore/rekor/blob/main/types.md#pkixx509.
// The resulting entry in Rekor has UUID
// `24296fb24b8ad77a51d549703a3a1c2dd2639ba49617fc563854031cb93e6d354e7b005065c334a8` and
// logIndex 30891523. The body of LogEntry can be fetched using `rekor-cli get --log-index
// 30891523`.
const LOG_ENTRY_PATH: &str = "testdata/logentry.json";

// Public key of the Rekor instance hosted by sigstore.dev. It is downloaded from
// https://rekor.sigstore.dev/api/v1/log/publicKey.
const REKOR_PUBLIC_KEY_PATH: &str = "testdata/rekor_public_key.pem";

struct TestData {
    endorsement: Vec<u8>,
    endorsement_signature: Vec<u8>,
    log_entry: Vec<u8>,
    endorser_public_key_pem: String,
    rekor_public_key_pem: String,
    endorser_public_key: Vec<u8>,
    rekor_public_key: Vec<u8>,
}

fn load_testdata() -> TestData {
    let endorsement = fs::read(ENDORSEMENT_PATH).expect("couldn't read endorsement");
    let endorsement_signature =
        fs::read(ENDORSEMENT_SIGNATURE_PATH).expect("couldn't read endorsement");
    let log_entry = fs::read(LOG_ENTRY_PATH).expect("couldn't read log entry");
    let endorser_public_key_pem =
        fs::read_to_string(ENDORSER_PUBLIC_KEY_PATH).expect("couldn't read endorser public key");
    let rekor_public_key_pem =
        fs::read_to_string(REKOR_PUBLIC_KEY_PATH).expect("couldn't read rekor public key");

    let endorser_public_key = convert_pem_to_raw(endorser_public_key_pem.as_str())
        .expect("failed to convert endorser key");
    let rekor_public_key =
        convert_pem_to_raw(&rekor_public_key_pem).expect("failed to convert Rekor key");

    TestData {
        endorsement,
        endorsement_signature,
        log_entry,
        endorser_public_key_pem,
        rekor_public_key_pem,
        endorser_public_key,
        rekor_public_key,
    }
}

#[test]
fn test_looks_like_pem() {
    let testdata = load_testdata();
    assert!(looks_like_pem(&testdata.endorser_public_key_pem));
    assert!(looks_like_pem(&testdata.rekor_public_key_pem));
    assert!(!looks_like_pem("-----BEGIN PUBLIC KEY-----\n"));
    assert!(!looks_like_pem("\n-----END PUBLIC KEY-----\n"));
    assert!(!looks_like_pem("whatever"));
}

#[test]
fn test_convert_from_pem() {
    let testdata = load_testdata();
    let key = pem_to_verifying_key(&testdata.rekor_public_key_pem);
    assert!(key.is_ok());
}

#[test]
fn test_convert_from_raw() {
    let testdata = load_testdata();
    let key = raw_to_verifying_key(&testdata.rekor_public_key);
    assert!(key.is_ok());
}

#[test]
fn test_convert_inverse_left() {
    let testdata = load_testdata();
    let pem = convert_raw_to_pem(&testdata.rekor_public_key);
    let actual = convert_pem_to_raw(&pem).expect("could not convert key");
    assert!(
        equal_keys(&testdata.rekor_public_key, &actual).expect("could not compare keys"),
        "{:?}",
        pem
    );
}

#[test]
fn test_convert_inverse_right() {
    let testdata = load_testdata();
    let raw = convert_pem_to_raw(&testdata.rekor_public_key_pem).expect("could not convert key");
    let actual = convert_raw_to_pem(&raw);
    assert!(
        actual.eq(&testdata.rekor_public_key_pem),
        "expected: {:?} actual: {:?}",
        &testdata.rekor_public_key_pem,
        actual
    );
}

#[test]
fn test_verify_signature() {
    let testdata = load_testdata();
    let result = verify_signature(
        &testdata.endorsement_signature,
        &testdata.endorsement,
        &testdata.endorser_public_key,
    );
    assert!(result.is_ok());
}

#[test]
fn test_verify_rekor_signature() {
    let testdata = load_testdata();
    let result = verify_rekor_signature(&testdata.log_entry, &testdata.rekor_public_key);
    assert!(result.is_ok());
}

#[test]
fn test_verify_rekor_log_entry() {
    let testdata = load_testdata();

    let result = verify_rekor_log_entry(
        &testdata.log_entry,
        &testdata.rekor_public_key,
        &testdata.endorsement,
    );
    assert!(result.is_ok(), "{:?}", result);
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
fn test_verify_endorsement_statement() {
    let testdata = load_testdata();
    let result =
        verify_endorsement_statement(&testdata.endorsement, BINARY_DIGEST.as_bytes(), "sha256");
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_endorser_public_key() {
    let testdata = load_testdata();

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement,
        rekor_log_entry: testdata.log_entry,
        base64_pem_encoded_rekor_public_key: BASE64_STANDARD.encode(&testdata.rekor_public_key_pem),
    };

    let result = verify_endorser_public_key(&binary_attestation, &testdata.endorser_public_key);
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_rekor_public_key() {
    let testdata = load_testdata();

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement,
        rekor_log_entry: testdata.log_entry,
        base64_pem_encoded_rekor_public_key: BASE64_STANDARD.encode(&testdata.rekor_public_key_pem),
    };

    let result = verify_rekor_public_key(&binary_attestation, &testdata.rekor_public_key);
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement() {
    let testdata = load_testdata();

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement,
        rekor_log_entry: testdata.log_entry,
        base64_pem_encoded_rekor_public_key: BASE64_STANDARD.encode(&testdata.rekor_public_key_pem),
    };

    let result = verify_binary_endorsement(
        BINARY_DIGEST.as_bytes(),
        "sha256",
        &binary_attestation,
        &testdata.endorser_public_key,
        &testdata.rekor_public_key,
    );
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_verify_binary_endorsement_fails_when_missing_digest() {
    let testdata = load_testdata();

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement,
        rekor_log_entry: testdata.log_entry,
        base64_pem_encoded_rekor_public_key: BASE64_STANDARD.encode(&testdata.rekor_public_key_pem),
    };

    let result = verify_binary_endorsement(
        BINARY_DIGEST.as_bytes(),
        "sha2-384",
        &binary_attestation,
        &testdata.endorser_public_key,
        &testdata.rekor_public_key,
    );
    assert!(result.is_err(), "{:?}", result);
    assert!(result
        .map_err(|err| format!("{err}"))
        .unwrap_err()
        .contains("missing sha2-384 digest"));
}

#[test]
fn test_verify_binary_endorsement_fails_with_invalid_rekor_public_key() {
    let testdata = load_testdata();

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement,
        rekor_log_entry: testdata.log_entry,
        // NB: We use the wrong key deliberately.
        base64_pem_encoded_rekor_public_key: BASE64_STANDARD
            .encode(&testdata.endorser_public_key_pem),
    };

    let result = verify_binary_endorsement(
        BINARY_DIGEST.as_bytes(),
        "sha256",
        &binary_attestation,
        &testdata.endorser_public_key,
        &testdata.rekor_public_key,
    );
    assert!(result.is_err(), "{:?}", result);
    assert!(result
        .map_err(|err| format!("{err}"))
        .unwrap_err()
        .contains("Rekor public key mismatch"));
}

#[test]
fn test_verify_binary_endorsement_fails_when_missing_rekor_entry() {
    let testdata = load_testdata();

    let binary_attestation = BinaryAttestation {
        endorsement_statement: testdata.endorsement,
        rekor_log_entry: Vec::new(),
        base64_pem_encoded_rekor_public_key: "".to_string(),
    };

    let result = verify_binary_endorsement(
        BINARY_DIGEST.as_bytes(),
        "sha256",
        &binary_attestation,
        &testdata.endorser_public_key,
        &testdata.rekor_public_key,
    );
    assert!(result.is_err(), "{:?}", result);
}
