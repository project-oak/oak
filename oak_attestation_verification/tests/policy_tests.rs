//
// Copyright 2024 The Project Oak Authors
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

#![feature(assert_matches)]

use core::assert_matches::assert_matches;
use std::{fs, sync::Arc};

use anyhow::Context;
use oak_attestation_verification::{
    policy::{
        application::ApplicationPolicy,
        container::ContainerPolicy,
        firmware::FirmwarePolicy,
        kernel::KernelPolicy,
        platform::AmdSevSnpPolicy,
        session_binding_public_key::{
            SessionBindingPublicKeyPolicy, SessionBindingPublicKeyVerificationError,
            SessionBindingPublicKeyVerificationReport,
        },
        system::SystemPolicy,
        SESSION_BINDING_PUBLIC_KEY_ID,
    },
    verifier::{
        AmdSevSnpDiceAttestationVerifier, EventLogVerifier, SoftwareRootedDiceAttestationVerifier,
    },
};
use oak_attestation_verification_types::{
    policy::{EventPolicy, Policy},
    verifier::AttestationVerifier,
};
use oak_crypto::{
    certificate::certificate_verifier::{CertificateVerificationReport, CertificateVerifier},
    verifier::Verifier,
};
use oak_file_utils::data_path;
use oak_proto_rust::{
    certificate::SESSION_BINDING_PUBLIC_KEY_PURPOSE_ID,
    oak::{
        attestation::v1::{
            binary_reference_value, endorsements, reference_values, AmdSevSnpEndorsement,
            CbReferenceValues, CertificateAuthorityEndorsement, Endorsements, Event, EventLog,
            Evidence, OakContainersReferenceValues, OakRestrictedKernelReferenceValues,
            ReferenceValues, SessionBindingPublicKeyData, SessionBindingPublicKeyEndorsement,
            SkipVerification,
        },
        crypto::v1::{
            Certificate, CertificatePayload, SignatureInfo, SubjectPublicKeyInfo, Validity,
        },
        Variant,
    },
};
use oak_sev_snp_attestation_report::AttestationReport;
use oak_time::{clock::FixedClock, Clock, Instant};
use prost::Message;
use prost_types::Timestamp;
use test_util::attestation_data::AttestationData;
use zerocopy::FromBytes;

const CB_EVIDENCE_SR_PATH: &str =
    "oak_attestation_verification/testdata/cb_evidence_software_rooted.binarypb";

const CERTIFICATE_EVENT_INDEX: usize = 0;
const KERNEL_EVENT_INDEX: usize = 0;
const RK_APPLICATION_EVENT_INDEX: usize = 1;
const SYSTEM_EVENT_INDEX: usize = 1;
const CONTAINER_EVENT_INDEX: usize = 2;

const TEST_PUBLIC_KEY: [u8; 4] = [0, 1, 2, 3];
const TEST_WRONG_PUBLIC_KEY: [u8; 4] = [4, 5, 6, 7];
const TEST_SIGNATURE: [u8; 4] = [8, 9, 10, 11];
const TEST_WRONG_SIGNATURE: [u8; 4] = [12, 13, 14, 15];

// A random time value used to parametrize test cases.
const TEST_TIME: Instant = Instant::from_unix_millis(1_000_000);

struct TestSignatureVerifier {
    pub expected_signature: Vec<u8>,
}

impl Verifier for TestSignatureVerifier {
    fn verify(&self, _message: &[u8], signature: &[u8]) -> anyhow::Result<()> {
        anyhow::ensure!(signature == self.expected_signature);
        Ok(())
    }
}

fn extract_attestation_report(evidence: &Evidence) -> anyhow::Result<&AttestationReport> {
    let root_layer =
        &evidence.root_layer.as_ref().context("root DICE layer wasn't provided in the evidence")?;
    AttestationReport::ref_from_bytes(&root_layer.remote_attestation_report)
        .map_err(|err| anyhow::anyhow!("invalid AMD SEV-SNP attestation report: {}", err))
}

fn get_oc_reference_values(reference_values: &ReferenceValues) -> OakContainersReferenceValues {
    let oc_reference_values = match reference_values.r#type.as_ref() {
        Some(reference_values::Type::OakContainers(containers_reference_values)) => {
            containers_reference_values.clone()
        }
        _ => panic!("couldn't find Oak Containers reference values"),
    };
    assert!(oc_reference_values.root_layer.is_some());
    assert!(oc_reference_values.root_layer.as_ref().unwrap().amd_sev.is_some());
    assert!(oc_reference_values.kernel_layer.is_some());
    assert!(oc_reference_values.system_layer.is_some());
    assert!(oc_reference_values.container_layer.is_some());
    oc_reference_values
}

fn get_rk_reference_values(
    reference_values: &ReferenceValues,
) -> OakRestrictedKernelReferenceValues {
    let rk_reference_values = match reference_values.r#type.as_ref() {
        Some(reference_values::Type::OakRestrictedKernel(rk_reference_values)) => {
            rk_reference_values.clone()
        }
        _ => panic!("couldn't find Oak Restricted Kernel reference values"),
    };
    assert!(rk_reference_values.root_layer.is_some());
    assert!(rk_reference_values.kernel_layer.is_some());
    assert!(rk_reference_values.application_layer.is_some());
    rk_reference_values
}

fn load_cb_evidence_software_rooted() -> Evidence {
    let serialized = fs::read(data_path(CB_EVIDENCE_SR_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

fn get_cb_reference_values(reference_values: &ReferenceValues) -> CbReferenceValues {
    let cb_reference_values = match reference_values.r#type.as_ref() {
        Some(reference_values::Type::Cb(cb_reference_values)) => cb_reference_values.clone(),
        _ => panic!("couldn't find CB reference values"),
    };
    assert!(cb_reference_values.root_layer.is_some());
    assert!(cb_reference_values.root_layer.as_ref().unwrap().amd_sev.is_some());
    assert!(!cb_reference_values.layers.is_empty());
    cb_reference_values
}

fn create_public_key_event(session_binding_public_key: &[u8]) -> Event {
    Event {
        tag: "session_binding_key".to_string(),
        event: Some(prost_types::Any {
            type_url: "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData"
                .to_string(),
            value: SessionBindingPublicKeyData {
                session_binding_public_key: session_binding_public_key.to_vec(),
            }
            .encode_to_vec(),
        }),
    }
}

fn create_public_key_evidence(session_binding_public_key: &[u8]) -> Evidence {
    let event = create_public_key_event(session_binding_public_key);
    Evidence {
        event_log: Some(EventLog { encoded_events: vec![event.encode_to_vec()] }),
        ..Default::default()
    }
}

fn create_test_certificate(signature: &[u8]) -> Certificate {
    let not_before = Timestamp { seconds: TEST_TIME.into_unix_seconds(), nanos: 0 };
    let not_after = Timestamp { seconds: not_before.seconds + 1, nanos: 999_999_999 };
    let validity = Validity { not_before: Some(not_before), not_after: Some(not_after) };
    let subject_public_key_info = SubjectPublicKeyInfo {
        public_key: TEST_PUBLIC_KEY.to_vec(),
        purpose_id: SESSION_BINDING_PUBLIC_KEY_PURPOSE_ID.to_vec(),
    };
    let payload = CertificatePayload {
        validity: Some(validity),
        subject_public_key_info: Some(subject_public_key_info),
        ..Default::default()
    };
    let serialized_payload = payload.encode_to_vec();

    Certificate {
        serialized_payload,
        signature_info: Some(SignatureInfo { signature: signature.to_vec() }),
    }
}

fn create_public_key_endorsement(signature: &[u8]) -> SessionBindingPublicKeyEndorsement {
    SessionBindingPublicKeyEndorsement {
        ca_endorsement: Some(CertificateAuthorityEndorsement {
            certificate: Some(create_test_certificate(signature)),
        }),
        ..Default::default()
    }
}

fn create_public_key_endorsements(signature: &[u8]) -> Endorsements {
    let ca_endorsement = create_public_key_endorsement(signature);
    Endorsements { events: vec![ca_endorsement.into()], ..Default::default() }
}

#[test]
fn cb_software_rooted_dice_verify_succeeds() {
    let clock = FixedClock::at_instant(TEST_TIME);
    let evidence = load_cb_evidence_software_rooted();
    let endorsements = Endorsements::default();

    let verifier = SoftwareRootedDiceAttestationVerifier::new(Arc::new(clock));

    let result = verifier.verify(&evidence, &endorsements);
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn cb_dice_verify_succeeds() {
    let d = AttestationData::load_cb();
    let clock = FixedClock::at_instant(d.make_valid_time());
    let ref_values = get_cb_reference_values(&d.reference_values);
    let platform_endorsement = AmdSevSnpEndorsement {
        tee_certificate: match d.endorsements.r#type.as_ref() {
            Some(endorsements::Type::Cb(e)) => {
                e.root_layer.as_ref().unwrap().tee_certificate.to_vec()
            }
            _ => vec![],
        },
    };
    let empty_variant: Variant = Variant::default();
    let endorsements = Endorsements {
        platform: Some(platform_endorsement.into()),
        initial: Some(empty_variant),
        ..Default::default()
    };

    let platform_reference_values =
        ref_values.root_layer.as_ref().unwrap().amd_sev.as_ref().unwrap();
    let platform_policy = AmdSevSnpPolicy::new(platform_reference_values);

    let firmware_reference_values =
        ref_values.root_layer.as_ref().unwrap().amd_sev.as_ref().unwrap().stage0.as_ref().unwrap();
    // TODO: b/375137648 - Use real reference once new endorsements are available.
    let mut skip_firmware_reference_values = firmware_reference_values.clone();
    skip_firmware_reference_values.r#type =
        Some(binary_reference_value::Type::Skip(SkipVerification {}));
    let firmware_policy = FirmwarePolicy::new(&skip_firmware_reference_values);

    let event_policies: Vec<Box<dyn EventPolicy>> = vec![];

    let verifier = AmdSevSnpDiceAttestationVerifier::new(
        platform_policy,
        Box::new(firmware_policy),
        event_policies,
        Arc::new(clock),
    );

    let result = verifier.verify(&d.evidence, &endorsements);
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn session_binding_key_policy_succeeds() {
    let evidence = create_public_key_evidence(&TEST_PUBLIC_KEY);
    let endorsements = create_public_key_endorsements(&TEST_SIGNATURE);

    let event = &evidence.event_log.as_ref().unwrap().encoded_events[CERTIFICATE_EVENT_INDEX];
    let endorsement = &endorsements.events[CERTIFICATE_EVENT_INDEX];

    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    let result = policy.verify(TEST_TIME, event, endorsement);
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn session_binding_key_policy_fails_with_incorrect_event_id() {
    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Incorrect event ID.
    let event_wrong_id = Event {
        tag: "session_binding_key".to_string(),
        event: Some(prost_types::Any {
            type_url: "wrong ID".to_string(),
            value: SessionBindingPublicKeyData {
                session_binding_public_key: TEST_PUBLIC_KEY.to_vec(),
            }
            .encode_to_vec(),
        }),
    }
    .encode_to_vec();
    let endorsement: Variant = create_public_key_endorsement(&TEST_SIGNATURE).into();
    let result = policy.verify(TEST_TIME, &event_wrong_id, &endorsement);
    assert!(result.is_err(), "Succeeded but expected a failure: {:?}", result.ok().unwrap());
}

#[test]
fn session_binding_key_policy_fails_with_incorrect_endorsement_id() {
    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Incorrect endorsement ID.
    let event = create_public_key_event(&TEST_PUBLIC_KEY).encode_to_vec();
    let endorsement_wrong_id = Variant {
        id: b"Wrong ID".to_vec(),
        value: create_public_key_endorsement(&TEST_SIGNATURE).encode_to_vec(),
    };
    let result = policy.verify(TEST_TIME, &event, &endorsement_wrong_id);
    assert!(result.is_err(), "Succeeded but expected a failure: {:?}", result.ok().unwrap());
}

#[test]
fn session_binding_key_policy_fails_with_empty_ca_endorsement() {
    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Empty CA endorsement.
    let event = create_public_key_event(&TEST_PUBLIC_KEY).encode_to_vec();
    let empty_ca_endorsement: Variant =
        SessionBindingPublicKeyEndorsement { ca_endorsement: None, ..Default::default() }.into();
    let result = policy.verify(TEST_TIME, &event, &empty_ca_endorsement);
    assert!(result.is_err(), "Succeeded but expected a failure: {:?}", result.ok().unwrap());
}

#[test]
fn session_binding_key_policy_fails_with_incorrect_public_key() {
    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Incorrect public key.
    let event_wrong_key = create_public_key_event(&TEST_WRONG_PUBLIC_KEY).encode_to_vec();
    let endorsement: Variant = create_public_key_endorsement(&TEST_SIGNATURE).into();
    let result = policy.verify(TEST_TIME, &event_wrong_key, &endorsement);
    assert!(result.is_err(), "Succeeded but expected a failure: {:?}", result.ok().unwrap());
}

#[test]
fn session_binding_key_policy_fails_with_empty_public_key() {
    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Empty public key.
    let event_empty_key = create_public_key_event(&[]).encode_to_vec();
    let endorsement: Variant = create_public_key_endorsement(&TEST_SIGNATURE).into();
    let result = policy.verify(TEST_TIME, &event_empty_key, &endorsement);
    assert!(result.is_err(), "Succeeded but expected a failure: {:?}", result.ok().unwrap());
}

#[test]
fn session_binding_key_policy_fails_with_invalid_signature() {
    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Invalid signature.
    let event = create_public_key_event(&TEST_PUBLIC_KEY).encode_to_vec();
    let endorsement_wrong_signature: Variant =
        create_public_key_endorsement(&TEST_WRONG_SIGNATURE).into();
    let result = policy.verify(TEST_TIME, &event, &endorsement_wrong_signature);
    assert!(result.is_err(), "Succeeded but expected a failure: {:?}", result.ok().unwrap());
}

#[test]
fn session_binding_key_policy_report_succeeds() {
    let evidence = create_public_key_evidence(&TEST_PUBLIC_KEY);
    let endorsements = create_public_key_endorsements(&TEST_SIGNATURE);

    let event = &evidence.event_log.as_ref().unwrap().encoded_events[CERTIFICATE_EVENT_INDEX];
    let endorsement = &endorsements.events[CERTIFICATE_EVENT_INDEX];

    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    let result = policy.report(TEST_TIME, event, endorsement);
    assert_matches!(
        result,
        Ok(SessionBindingPublicKeyVerificationReport {
            endorsement: Ok(CertificateVerificationReport {
                validity: Ok(()),
                verification: Ok(()),
                freshness: None,
            }),
            ..
        })
    );
}

#[test]
fn session_binding_key_policy_report_fails_with_incorrect_event_id() {
    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Incorrect event ID.
    let event_wrong_id = Event {
        tag: "session_binding_key".to_string(),
        event: Some(prost_types::Any {
            type_url: "wrong ID".to_string(),
            value: SessionBindingPublicKeyData {
                session_binding_public_key: TEST_PUBLIC_KEY.to_vec(),
            }
            .encode_to_vec(),
        }),
    }
    .encode_to_vec();
    let endorsement: Variant = create_public_key_endorsement(&TEST_SIGNATURE).into();
    let result = policy.report(TEST_TIME, &event_wrong_id, &endorsement);
    assert_matches!(result, Err(SessionBindingPublicKeyVerificationError::ProtoDecodeError(_)));
}

#[test]
fn session_binding_key_policy_report_fails_with_incorrect_endorsement_id() {
    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Incorrect endorsement ID.
    let event = create_public_key_event(&TEST_PUBLIC_KEY).encode_to_vec();
    let endorsement_wrong_id = Variant {
        id: b"Wrong ID".to_vec(),
        value: create_public_key_endorsement(&TEST_SIGNATURE).encode_to_vec(),
    };
    let result = policy.report(TEST_TIME, &event, &endorsement_wrong_id);
    assert_matches!(result, Err(SessionBindingPublicKeyVerificationError::VariantDecodeError(_)));
}

#[test]
fn session_binding_key_policy_report_fails_with_empty_ca_endorsement() {
    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Empty CA endorsement.
    let event = create_public_key_event(&TEST_PUBLIC_KEY).encode_to_vec();
    let empty_ca_endorsement: Variant =
        SessionBindingPublicKeyEndorsement { ca_endorsement: None, ..Default::default() }.into();
    let result = policy.report(TEST_TIME, &event, &empty_ca_endorsement);
    assert_matches!(
        result,
        Err(SessionBindingPublicKeyVerificationError::MissingField(
            "SessionBindingPublicKeyEndorsement.ca_endorsement"
        ))
    );
}

#[test]
fn session_binding_key_policy_report_fails_with_incorrect_public_key() {
    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Incorrect public key.
    let event_wrong_key = create_public_key_event(&TEST_WRONG_PUBLIC_KEY).encode_to_vec();
    let endorsement: Variant = create_public_key_endorsement(&TEST_SIGNATURE).into();
    let result = policy.report(TEST_TIME, &event_wrong_key, &endorsement);
    assert_matches!(
        result,
        Ok(SessionBindingPublicKeyVerificationReport {
            endorsement: Ok(CertificateVerificationReport {
                validity: Ok(()),
                verification: Err(_),
                freshness: None,
            }),
            ..
        })
    );
}

#[test]
fn session_binding_key_policy_report_fails_with_empty_public_key() {
    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Empty public key.
    let event_empty_key = create_public_key_event(&[]).encode_to_vec();
    let endorsement: Variant = create_public_key_endorsement(&TEST_SIGNATURE).into();
    let result = policy.report(TEST_TIME, &event_empty_key, &endorsement);
    assert_matches!(
        result,
        Err(SessionBindingPublicKeyVerificationError::MissingField(
            "SessionBindingPublicKeyData.session_binding_public_key"
        ))
    );
}

#[test]
fn session_binding_key_policy_report_fails_with_invalid_signature() {
    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Invalid signature.
    let event = create_public_key_event(&TEST_PUBLIC_KEY).encode_to_vec();
    let endorsement_wrong_signature: Variant =
        create_public_key_endorsement(&TEST_WRONG_SIGNATURE).into();
    let result = policy.report(TEST_TIME, &event, &endorsement_wrong_signature);
    assert_matches!(
        result,
        Ok(SessionBindingPublicKeyVerificationReport {
            endorsement: Ok(CertificateVerificationReport {
                validity: Ok(()),
                verification: Err(_),
                freshness: None,
            }),
            ..
        })
    );
}

#[test]
fn event_log_verifier_succeeds() {
    let clock = FixedClock::at_instant(TEST_TIME);
    let evidence = create_public_key_evidence(&TEST_PUBLIC_KEY);
    let endorsements = create_public_key_endorsements(&TEST_SIGNATURE);

    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Create verifier.
    let verifier = EventLogVerifier::new(vec![Box::new(policy)], Arc::new(clock));
    let result = verifier.verify(&evidence, &endorsements);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());

    // Check that the policy correctly extracts the public key.
    let event_attestation_results = result.unwrap().event_attestation_results;
    assert!(event_attestation_results.len() == 1);
    let extracted_public_key =
        event_attestation_results[0].artifacts.get(SESSION_BINDING_PUBLIC_KEY_ID);
    assert!(extracted_public_key.is_some());
    assert!(*extracted_public_key.unwrap() == TEST_PUBLIC_KEY);
}

#[test]
fn event_log_verifier_fails() {
    let clock = FixedClock::at_instant(TEST_TIME);
    let evidence = create_public_key_evidence(&TEST_PUBLIC_KEY);
    let endorsements = create_public_key_endorsements(&TEST_WRONG_SIGNATURE);

    let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
        CertificateVerifier::new(TestSignatureVerifier {
            expected_signature: TEST_SIGNATURE.to_vec(),
        });
    let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

    // Create verifier.
    let verifier = EventLogVerifier::new(vec![Box::new(policy)], Arc::new(clock));
    let result = verifier.verify(&evidence, &endorsements);

    assert!(result.is_err(), "Succeeded but expected a failure: {:?}", result.ok().unwrap());
}

#[test]
fn oc_amd_sev_snp_platform_policy_verify_succeeds() {
    let d = AttestationData::load_milan_oc_release();
    let ref_values = get_oc_reference_values(&d.reference_values);
    let platform_reference_values =
        ref_values.root_layer.as_ref().unwrap().amd_sev.as_ref().unwrap();
    let policy = AmdSevSnpPolicy::new(platform_reference_values);
    let attestation_report = extract_attestation_report(&d.evidence).unwrap();
    let endorsement = AmdSevSnpEndorsement {
        tee_certificate: match d.endorsements.r#type.as_ref() {
            Some(endorsements::Type::OakContainers(e)) => {
                e.root_layer.as_ref().unwrap().tee_certificate.to_vec()
            }
            _ => vec![],
        },
    };

    let result = policy.verify(d.make_valid_time(), attestation_report, &endorsement.into());

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn oc_amd_sev_snp_firmware_policy_verify_succeeds() {
    let d = AttestationData::load_milan_oc_release();
    let ref_values = get_oc_reference_values(&d.reference_values);
    let firmware_reference_values =
        ref_values.root_layer.as_ref().unwrap().amd_sev.as_ref().unwrap().stage0.as_ref().unwrap();
    let policy = FirmwarePolicy::new(firmware_reference_values);

    let firmware_measurement = &extract_attestation_report(&d.evidence).unwrap().data.measurement;
    let firmware_endorsement = d.endorsements.initial.as_ref().unwrap();

    let result = policy.verify(d.make_valid_time(), firmware_measurement, firmware_endorsement);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn oc_kernel_policy_verify_succeeds() {
    let d = AttestationData::load_milan_oc_release();
    let ref_values = get_oc_reference_values(&d.reference_values);
    let policy = KernelPolicy::new(ref_values.kernel_layer.as_ref().unwrap());
    let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];
    let endorsement = &d.endorsements.events[KERNEL_EVENT_INDEX];

    let result = policy.verify(d.make_valid_time(), event, endorsement);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn oc_system_policy_verify_succeeds() {
    let d = AttestationData::load_milan_oc_release();
    let ref_values = get_oc_reference_values(&d.reference_values);
    let policy = SystemPolicy::new(ref_values.system_layer.as_ref().unwrap());
    let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[SYSTEM_EVENT_INDEX];
    let endorsement = &d.endorsements.events[SYSTEM_EVENT_INDEX];

    let result = policy.verify(d.make_valid_time(), event, endorsement);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn oc_container_policy_verify_succeeds() {
    let d = AttestationData::load_milan_oc_release();
    let ref_values = get_oc_reference_values(&d.reference_values);
    // TODO: b/382550581 - Container reference values currently skip verification.
    let policy = ContainerPolicy::new(ref_values.container_layer.as_ref().unwrap());
    let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[CONTAINER_EVENT_INDEX];
    let endorsement = &d.endorsements.events[CONTAINER_EVENT_INDEX];

    let result = policy.verify(d.make_valid_time(), event, endorsement);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn rk_kernel_policy_verify_succeeds() {
    let d: AttestationData = AttestationData::load_milan_rk_release();
    let ref_values = get_rk_reference_values(&d.reference_values);
    let kernel_ref_values = ref_values.kernel_layer.as_ref().unwrap();
    let policy = KernelPolicy::new(kernel_ref_values);
    let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];
    let endorsement = &d.endorsements.events[KERNEL_EVENT_INDEX];

    let result = policy.verify(d.make_valid_time(), event, endorsement);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn rk_application_policy_verify_succeeds() {
    let d = AttestationData::load_milan_rk_release();
    let ref_values = get_rk_reference_values(&d.reference_values);
    // TODO: b/382550581 - Application reference values currently skip verification.
    let app_ref_values = ref_values.application_layer.as_ref().unwrap();
    let policy = ApplicationPolicy::new(app_ref_values);
    let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[RK_APPLICATION_EVENT_INDEX];
    let endorsement = &d.endorsements.events[RK_APPLICATION_EVENT_INDEX];

    let result = policy.verify(d.make_valid_time(), event, endorsement);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

// Creates an AmdSevSnpDiceAttestationVerifier from reference values.
// This function could become part of the public API.
fn create_verifier<T: Clock + 'static>(
    clock: T,
    reference_values: &ReferenceValues,
) -> anyhow::Result<AmdSevSnpDiceAttestationVerifier> {
    match reference_values.r#type.as_ref() {
        Some(reference_values::Type::OakContainers(rvs)) => {
            let root_rvs = rvs.root_layer.as_ref().context("no root layer reference values")?;
            let platform_policy = AmdSevSnpPolicy::from_root_layer_reference_values(root_rvs)
                .context("failed to create platform policy")?;
            let firmware_policy = FirmwarePolicy::from_root_layer_reference_values(root_rvs)
                .context("failed to create firmware policy")?;
            let kernel_policy = KernelPolicy::new(
                rvs.kernel_layer.as_ref().context("no kernel layer reference values")?,
            );
            let system_policy = SystemPolicy::new(
                rvs.system_layer.as_ref().context("no system layer reference values")?,
            );
            // TODO: b/382550581 - Container reference values currently skip verification.
            let container_policy = ContainerPolicy::new(
                rvs.container_layer.as_ref().context("no container layer reference values")?,
            );
            let event_policies: Vec<Box<dyn Policy<[u8]>>> =
                vec![Box::new(kernel_policy), Box::new(system_policy), Box::new(container_policy)];

            Ok(AmdSevSnpDiceAttestationVerifier::new(
                platform_policy,
                Box::new(firmware_policy),
                event_policies,
                Arc::new(clock),
            ))
        }
        Some(reference_values::Type::OakRestrictedKernel(rvs)) => {
            // Create platform and firmware policies.
            // TODO: b/398859203 - Remove root layer reference values once old reference
            // values have been updated.
            let root_rvs = rvs.root_layer.as_ref().context("no root layer reference values")?;
            let platform_policy = AmdSevSnpPolicy::from_root_layer_reference_values(root_rvs)
                .context("failed to create platform policy")?;
            let firmware_policy = FirmwarePolicy::from_root_layer_reference_values(root_rvs)
                .context("failed to create firmware policy")?;
            let kernel_policy = KernelPolicy::new(
                rvs.kernel_layer.as_ref().context("no kernel layer reference values")?,
            );
            // TODO: b/382550581 - Application reference values currently skip verification.
            let application_policy = ApplicationPolicy::new(
                rvs.application_layer.as_ref().context("no application layer reference values")?,
            );
            let event_policies: Vec<Box<dyn Policy<[u8]>>> =
                vec![Box::new(kernel_policy), Box::new(application_policy)];

            Ok(AmdSevSnpDiceAttestationVerifier::new(
                platform_policy,
                Box::new(firmware_policy),
                event_policies,
                Arc::new(clock),
            ))
        }
        _ => anyhow::bail!("malformed reference values"),
    }
}

macro_rules! test_amd_sev_snp_verifier_success {
    ($($name:tt)*) => {
        mod test_amd_sev_snp_verifier_success {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let d = AttestationData::$name();
                    let clock = FixedClock::at_instant(d.make_valid_time());
                    let verifier = create_verifier(clock, &d.reference_values).expect("failed to create verifier");

                    let result = verifier.verify(&d.evidence, &d.endorsements);

                    // TODO: b/356631062 - Verify detailed attestation results.
                    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
                }
            )*
        }
    }
}

test_amd_sev_snp_verifier_success! {
    load_milan_oc_release
    load_milan_oc_staging
    // Requires event-based endorsements for both. Enable once we have them.
    // load_genoa_oc
    // load_turin_oc
    load_milan_rk_release
    load_milan_rk_staging
}
