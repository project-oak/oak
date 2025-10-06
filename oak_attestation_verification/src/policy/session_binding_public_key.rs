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

use alloc::vec::Vec;

use oak_attestation_verification_types::policy::Policy;
use oak_crypto::{
    certificate::certificate_verifier::{
        CertificateVerificationError, CertificateVerificationReport, CertificateVerifier,
    },
    verifier::Verifier,
};
use oak_proto_rust::{
    certificate::SESSION_BINDING_PUBLIC_KEY_PURPOSE_ID,
    oak::{
        attestation::v1::{
            EventAttestationResults, SessionBindingPublicKeyData,
            SessionBindingPublicKeyEndorsement,
        },
        Variant,
    },
};
use oak_time::Instant;

use crate::{results::set_session_binding_public_key, util::decode_event_proto};

#[derive(Debug)]
pub struct SessionBindingPublicKeyVerificationReport {
    pub session_binding_public_key: Vec<u8>,
    pub endorsement: Result<CertificateVerificationReport, CertificateVerificationError>,
}

impl SessionBindingPublicKeyVerificationReport {
    pub fn into_session_binding_public_key(
        self,
    ) -> Result<Vec<u8>, SessionBindingPublicKeyVerificationError> {
        match self {
            SessionBindingPublicKeyVerificationReport {
                session_binding_public_key,
                endorsement: Ok(certificate_verification_report),
            } => Ok(certificate_verification_report
                .into_checked()
                .map(|_| session_binding_public_key)?),
            SessionBindingPublicKeyVerificationReport {
                session_binding_public_key: _,
                endorsement: Err(err),
            } => Err(SessionBindingPublicKeyVerificationError::CertificateVerificationError(err)),
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum SessionBindingPublicKeyVerificationError {
    #[error("Missing field: {0}")]
    MissingField(&'static str),
    #[error("Failed to decode proto: {0}")]
    ProtoDecodeError(#[from] anyhow::Error),
    #[error("Failed to decode Variant: {0}")]
    VariantDecodeError(&'static str),
    #[error("Certificate verification failed: {0}")]
    CertificateVerificationError(#[from] CertificateVerificationError),
}

pub struct SessionBindingPublicKeyPolicy<V: Verifier> {
    certificate_verifier: CertificateVerifier<V>,
}

impl<V: Verifier> SessionBindingPublicKeyPolicy<V> {
    pub fn new(certificate_verifier: CertificateVerifier<V>) -> Self {
        Self { certificate_verifier }
    }

    // This is a copy of verify() except that it returns a report of the results
    // of running as many verification checks as possible (i.e. no fail-fast).
    pub fn report(
        &self,
        current_time: Instant,
        encoded_event: &[u8],
        encoded_endorsement: &Variant,
    ) -> Result<SessionBindingPublicKeyVerificationReport, SessionBindingPublicKeyVerificationError>
    {
        let event = decode_event_proto::<SessionBindingPublicKeyData>(
            "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData",
            encoded_event,
        )?;
        if event.session_binding_public_key.is_empty() {
            return Err(SessionBindingPublicKeyVerificationError::MissingField(
                "SessionBindingPublicKeyData.session_binding_public_key",
            ));
        }

        let ca_endorsement = <&Variant as TryInto<SessionBindingPublicKeyEndorsement>>::try_into(
            encoded_endorsement,
        )
        .map_err(SessionBindingPublicKeyVerificationError::VariantDecodeError)?
        .ca_endorsement
        .ok_or(SessionBindingPublicKeyVerificationError::MissingField(
            "SessionBindingPublicKeyEndorsement.ca_endorsement",
        ))?;
        let certificate = ca_endorsement.certificate.as_ref().ok_or(
            SessionBindingPublicKeyVerificationError::MissingField(
                "CertificateAuthorityEndorsement.certificate",
            ),
        )?;

        Ok(SessionBindingPublicKeyVerificationReport {
            session_binding_public_key: event.session_binding_public_key.clone(),
            endorsement: self.certificate_verifier.report(
                current_time,
                &event.session_binding_public_key,
                &SESSION_BINDING_PUBLIC_KEY_PURPOSE_ID,
                certificate,
            ),
        })
    }
}

// We have to use [`Policy<[u8]>`] instead of [`EventPolicy`], because
// Rust doesn't yet support implementing trait aliases.
// <https://github.com/rust-lang/rfcs/blob/master/text/1733-trait-alias.md>
impl<V: Verifier> Policy<[u8]> for SessionBindingPublicKeyPolicy<V> {
    fn verify(
        &self,
        current_time: Instant,
        evidence: &[u8],
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        let report = self.report(current_time, evidence, endorsement)?;
        let mut results = EventAttestationResults { ..Default::default() };
        set_session_binding_public_key(&mut results, &report.into_session_binding_public_key()?);
        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use alloc::sync::Arc;
    use core::assert_matches::assert_matches;

    use oak_attestation_verification_results::get_session_binding_public_key;
    use oak_attestation_verification_types::verifier::AttestationVerifier;
    use oak_proto_rust::oak::{
        attestation::v1::{
            CertificateAuthorityEndorsement, Endorsements, Event, EventLog, Evidence,
        },
        crypto::v1::{Certificate, CertificatePayload, SignatureInfo, SubjectPublicKeyInfo},
        Validity,
    };
    use oak_time::clock::FixedClock;
    use prost::Message;
    use prost_types::Timestamp;

    use super::*;
    use crate::EventLogVerifier;

    const TEST_PUBLIC_KEY: [u8; 4] = [0, 1, 2, 3];
    const TEST_WRONG_PUBLIC_KEY: [u8; 4] = [4, 5, 6, 7];
    const TEST_SIGNATURE: [u8; 4] = [8, 9, 10, 11];
    const TEST_WRONG_SIGNATURE: [u8; 4] = [12, 13, 14, 15];

    // A random time value used to parametrize test cases.
    const TEST_TIME: Instant = Instant::from_unix_millis(1_000_000);

    const CERTIFICATE_EVENT_INDEX: usize = 0;

    struct TestSignatureVerifier {
        pub expected_signature: Vec<u8>,
    }

    impl Verifier for TestSignatureVerifier {
        fn verify(&self, _message: &[u8], signature: &[u8]) -> anyhow::Result<()> {
            anyhow::ensure!(signature == self.expected_signature);
            Ok(())
        }
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
    fn verify_succeeds() {
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
    fn verify_fails_with_incorrect_event_id() {
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
    fn verify_fails_with_incorrect_endorsement_id() {
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
    fn verify_fails_with_empty_ca_endorsement() {
        let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
            CertificateVerifier::new(TestSignatureVerifier {
                expected_signature: TEST_SIGNATURE.to_vec(),
            });
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

        // Empty CA endorsement.
        let event = create_public_key_event(&TEST_PUBLIC_KEY).encode_to_vec();
        let empty_ca_endorsement: Variant =
            SessionBindingPublicKeyEndorsement { ca_endorsement: None, ..Default::default() }
                .into();
        let result = policy.verify(TEST_TIME, &event, &empty_ca_endorsement);
        assert!(result.is_err(), "Succeeded but expected a failure: {:?}", result.ok().unwrap());
    }

    #[test]
    fn verify_fails_with_incorrect_public_key() {
        let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
            CertificateVerifier::new(TestSignatureVerifier {
                expected_signature: TEST_SIGNATURE.to_vec(),
            });
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);
        let incorrect_key = create_public_key_event(&TEST_WRONG_PUBLIC_KEY).encode_to_vec();
        let endorsement: Variant = create_public_key_endorsement(&TEST_SIGNATURE).into();

        let result = policy.verify(TEST_TIME, &incorrect_key, &endorsement);

        assert!(result.is_err(), "Succeeded but expected a failure: {:?}", result.ok().unwrap());
    }

    #[test]
    fn verify_fails_with_empty_public_key() {
        let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
            CertificateVerifier::new(TestSignatureVerifier {
                expected_signature: TEST_SIGNATURE.to_vec(),
            });
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);
        let empty_key = create_public_key_event(&[]).encode_to_vec();
        let endorsement: Variant = create_public_key_endorsement(&TEST_SIGNATURE).into();

        let result = policy.verify(TEST_TIME, &empty_key, &endorsement);

        assert!(result.is_err(), "Succeeded but expected a failure: {:?}", result.ok().unwrap());
    }

    #[test]
    fn verify_fails_with_invalid_signature() {
        let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
            CertificateVerifier::new(TestSignatureVerifier {
                expected_signature: TEST_SIGNATURE.to_vec(),
            });
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);
        let event = create_public_key_event(&TEST_PUBLIC_KEY).encode_to_vec();
        let invalid_signature: Variant =
            create_public_key_endorsement(&TEST_WRONG_SIGNATURE).into();

        let result = policy.verify(TEST_TIME, &event, &invalid_signature);

        assert!(result.is_err(), "Succeeded but expected a failure: {:?}", result.ok().unwrap());
    }

    #[test]
    fn report_succeeds() {
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
    fn report_fails_with_incorrect_event_id() {
        let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
            CertificateVerifier::new(TestSignatureVerifier {
                expected_signature: TEST_SIGNATURE.to_vec(),
            });
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);
        let incorrect_event = Event {
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

        let result = policy.report(TEST_TIME, &incorrect_event, &endorsement);

        assert_matches!(result, Err(SessionBindingPublicKeyVerificationError::ProtoDecodeError(_)));
    }

    #[test]
    fn report_fails_with_incorrect_endorsement_id() {
        let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
            CertificateVerifier::new(TestSignatureVerifier {
                expected_signature: TEST_SIGNATURE.to_vec(),
            });
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);
        let event = create_public_key_event(&TEST_PUBLIC_KEY).encode_to_vec();
        let incorrect_endorsement = Variant {
            id: b"Wrong ID".to_vec(),
            value: create_public_key_endorsement(&TEST_SIGNATURE).encode_to_vec(),
        };

        let result = policy.report(TEST_TIME, &event, &incorrect_endorsement);

        assert_matches!(
            result,
            Err(SessionBindingPublicKeyVerificationError::VariantDecodeError(_))
        );
    }

    #[test]
    fn report_fails_with_empty_ca_endorsement() {
        let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
            CertificateVerifier::new(TestSignatureVerifier {
                expected_signature: TEST_SIGNATURE.to_vec(),
            });
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);
        let event = create_public_key_event(&TEST_PUBLIC_KEY).encode_to_vec();
        let empty_ca_endorsement: Variant =
            SessionBindingPublicKeyEndorsement { ca_endorsement: None, ..Default::default() }
                .into();

        let result = policy.report(TEST_TIME, &event, &empty_ca_endorsement);

        assert_matches!(
            result,
            Err(SessionBindingPublicKeyVerificationError::MissingField(
                "SessionBindingPublicKeyEndorsement.ca_endorsement"
            ))
        );
    }

    #[test]
    fn report_fails_with_incorrect_public_key() {
        let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
            CertificateVerifier::new(TestSignatureVerifier {
                expected_signature: TEST_SIGNATURE.to_vec(),
            });
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);
        let incorrect_key = create_public_key_event(&TEST_WRONG_PUBLIC_KEY).encode_to_vec();
        let endorsement: Variant = create_public_key_endorsement(&TEST_SIGNATURE).into();

        let result = policy.report(TEST_TIME, &incorrect_key, &endorsement);

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
    fn report_fails_with_empty_public_key() {
        let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
            CertificateVerifier::new(TestSignatureVerifier {
                expected_signature: TEST_SIGNATURE.to_vec(),
            });
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);
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
    fn report_fails_with_invalid_signature() {
        let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
            CertificateVerifier::new(TestSignatureVerifier {
                expected_signature: TEST_SIGNATURE.to_vec(),
            });
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);
        let event = create_public_key_event(&TEST_PUBLIC_KEY).encode_to_vec();
        let invalid_signature: Variant =
            create_public_key_endorsement(&TEST_WRONG_SIGNATURE).into();

        let result = policy.report(TEST_TIME, &event, &invalid_signature);

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
    fn event_log_verifier_success() {
        let clock = FixedClock::at_instant(TEST_TIME);
        let evidence = create_public_key_evidence(&TEST_PUBLIC_KEY);
        let endorsements = create_public_key_endorsements(&TEST_SIGNATURE);
        let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
            CertificateVerifier::new(TestSignatureVerifier {
                expected_signature: TEST_SIGNATURE.to_vec(),
            });
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

        let verifier = EventLogVerifier::new(vec![Box::new(policy)], Arc::new(clock));
        let result = verifier.verify(&evidence, &endorsements);

        // TODO: b/356631062 - Verify detailed attestation results.
        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());

        // Check that the policy correctly extracts the public key.
        let results = result.unwrap();
        assert!(results.event_attestation_results.len() == 1);
        let extracted_public_key = get_session_binding_public_key(&results);
        assert!(extracted_public_key.is_some());
        assert!(*extracted_public_key.unwrap() == TEST_PUBLIC_KEY);
    }

    #[test]
    fn event_log_verifier_failure() {
        let clock = FixedClock::at_instant(TEST_TIME);
        let evidence = create_public_key_evidence(&TEST_PUBLIC_KEY);
        let endorsements = create_public_key_endorsements(&TEST_WRONG_SIGNATURE);
        let certificate_verifier: CertificateVerifier<TestSignatureVerifier> =
            CertificateVerifier::new(TestSignatureVerifier {
                expected_signature: TEST_SIGNATURE.to_vec(),
            });
        let policy = SessionBindingPublicKeyPolicy::new(certificate_verifier);

        let verifier = EventLogVerifier::new(vec![Box::new(policy)], Arc::new(clock));
        let result = verifier.verify(&evidence, &endorsements);

        assert!(result.is_err(), "Succeeded but expected a failure: {:?}", result.ok().unwrap());
    }
}
