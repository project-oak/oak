// Copyright 2026 The Project Oak Authors
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

use alloc::{string::ToString, vec};

use oak_digest::{Sha2Digest, Sha256Hasher};
use oak_proto_rust::{
    google::pes::v1::{
        EcdsaP256PublicKey, PublicEndorsement, Signature, Statement, TLogReceipt,
        VerificationMaterial, X509Der, statement::Format as StatementFormat,
        verification_material::VerificationMaterial as VmOneof,
    },
    oak::{
        HexDigest,
        attestation::v1::{
            Claim, ClaimReferenceValue, Endorsement, KeyType, PesEndorsementReferenceValue,
            VerifyingKey, VerifyingKeySet, endorsement::Format as EndorsementFormat,
        },
    },
};
use oak_time::Instant;
use rsa::{Pkcs1v15Sign, RsaPrivateKey, pkcs8::EncodePublicKey};

use super::*;

pub(crate) const TEST_RSA_2048_PKCS8_DER_B64: &str = "\
MIIEvAIBADANBgkqhkiG9w0BAQEFAASCBKYwggSiAgEAAoIBAQCuLvnJf0gAqeKPn6NQrLBJWKd+\
quDFw5jrCmWRseXqAdgkpluhp0wnnxieqzK/0Z6eelVkSogJwggkTkMU1y4vc/K2BsaABj7+sCcC\
h0DlTJHWaE1P6VHsH0gVHQX7y1MB6KT5lqTnIfV4IeMpkrvUZVyF5knwJGTXZxpSKi1iMpec95Gs\
0ellgq1kcHFyi/tNYwlcH/tRLlgWPNoHZjeZJH0LHJWOROLwacPW7odFYRvShIv2mtGHz2Yl0T0W\
EJaV9a63gl5mczc/Ust9MA1NG6odXExHaXGBVSYewt6tv+7CdCboq4LKNUG/BU6jowBmWlFJNIsa\
fPEzRgEuASLPAgMBAAECggEACS5rtz3Qz0wlJ5nsE2AO6MbWCVy7fWEqidUh9nSQoG2ZdZEZSmOV\
pY8CzrZKdgb4G/Vp0+AD3LPQFw3TBmGzSwgLFqIzy2LI5kblv4Hen1eSZmFYFerACTi65XYCrzuP\
9A1NyOQybAaDuGHc5f+YjAENx/cUFabtc9c48XTMsJzQ0hnGXLl8JVzCU6c5x5qd2myHXyrEHO8O\
hX1pgKcNNIvGZ5y841dwGB7Np35l87zrAkXbH/TKz+cblmj675JqEXajeJbcO3p4tg2sN35MrE+7\
u1TCQDAOV7GhZKsOsM8dBU57rStaLbzM/ddVVHKMxmdBhnOlGCmqC/xHSfsJ1QKBgQDXGiOU/130\
i6CLMq/o/vfieq8Gbp86dToZCUExmZiOyReaVZJwELaVxsrPT62g+98R9m9paGgsfr8HcmMxNit0\
pfXum+/sJQzLj3bCDrxU7P06wFBAtPdBSXq+nvtPaEh5G444rsb0JHalFkfMlLT3qcOSQ4KbouH1\
o+hL0K0RYwKBgQDPTSsHDW6OaRnF+cLMWG0eyR160S8kQgXZjwted1JuaOVagp46rc/aZ55OEE8h\
yMuImrGeLbe4NueTPauHZ+QfKuXt43L24WraXN5/10YraswQDt2ckJuTDrBqqeAi5qALnKJY0RFB\
Kae7svra9woamYjITqPaEJQcv59FqtG6pQKBgHcqOPorew6mZ9uVyhSHZCapFtu2XyoQlY4XLXHg\
CL9ZsmTC8Wx6JdzWE7dECgm8X7lg0BoSSFwWH5hti3xQ6UQnSRbWdtVZNTx0jzM03Ksj26o3rn4a\
gzw9C+4cv1cfi77kQCcw1HGe3cfZjw9MdvEZsIoQMoQseYgPNPsDcU3HAoGATOOedfsxanjpKlk9\
O3YA405NNOSpy5UBfnRkDyHK3VDi4PNZpQIa+jM8sE+0Sh+j/oMCJl1mq1kSA7b4DD0oi7bpmZan\
aZKqg1u220wJpsjx73LUF+I7Egx8utNPYyKPcj8iqDbDY5wDrsbv7I98m+keps0kURmdFhytArYd\
HFECgYBGFRe4tFnyyvQOwHNruVU6K9gMZbpafMY8mVQlagVzVsAbTZHAbztmDHBxrimEJk3PbYea\
6Oc1tkGAVKRUqRUP+Il2H8cISU+hjqg/uBKs685h10SXOs8hJy86XwaPLtfYzCQlLBZLmiAIwKjg\
A1edf0NSAidb4q69a5aAcE+c+w==";

fn create_test_pes_confirmation_bytes(
    endorsement_bytes: &[u8],
) -> (Vec<u8>, VerifyingKeySet, VerifyingKey) {
    use base64::Engine;
    use rsa::pkcs8::DecodePrivateKey;
    let dummy_endorser_key_hex = "3059301306072a8648ce3d020106082a8648ce3d030107034200048b159e54b0cda5de273bf535ae7cd5946680dbfb87b6cc1348373b78de32806a7f26bb00459ba16edce02221acd1c4a0a45c9e627784dd4590f3bb29c98637f8";
    let dummy_endorser_key_bytes = hex::decode(dummy_endorser_key_hex).unwrap();

    let cert_base64 = "MIIDDTCCAfWgAwIBAgIUPBaPsaiMewIvsmo7QISZwW5kQHMwDQYJKoZIhvcNAQELBQAwFjEUMBIG\
A1UEAwwLdGVzdF9pc3N1ZXIwHhcNMjYwNTA3MTU1MjM3WhcNMjcwNTA3MTU1MjM3WjAWMRQwEgYD\
VQQDDAt0ZXN0X2lzc3VlcjCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEBAK4u+cl/SACp\
4o+fo1CssElYp36q4MXDmOsKZZGx5eoB2CSmW6GnTCefGJ6rMr/Rnp56VWRKiAnCCCROQxTXLi9z\
8rYGxoAGPv6wJwKHQOVMkdZoTU/pUewfSBUdBfvLUwHopPmWpOch9Xgh4ymSu9RlXIXmSfAkZNdn\
GlIqLWIyl5z3kazR6WWCrWRwcXKL+01jCVwf+1EuWBY82gdmN5kkfQsclY5E4vBpw9buh0VhG9KE\
i/aa0YfPZiXRPRYQlpX1rreCXmZzNz9Sy30wDU0bqh1cTEdpcYFVJh7C3q2/7sJ0Juirgso1Qb8F\
TqOjAGZaUUk0ixp88TNGAS4BIs8CAwEAAaNTMFEwHQYDVR0OBBYEFBrhSgVcGhgGwHV0OvgMbaDd\
m2jbMB8GA1UdIwQYMBaAFBrhSgVcGhgGwHV0OvgMbaDdm2jbMA8GA1UdEwEB/wQFMAMBAf8wDQYJ\
KoZIhvcNAQELBQADggEBAAlrMuM8629s0VOJAVn46HzgKXgYCqNJHqkUQEn1X+6RznYRzQD2xz7n\
yoHZGCFmRZZKJzDLwToDECDYcte+JDoFlSsGoDaMaSueSBWWilmv3Du64XNIu9syQwLUS8ehtr/P\
s3rndIOZ92m4mUuXtzj9VOu0eiKL3bi0xT/w7Dp5hmD71tOrpndZA3b29fqEifFGDc/XatIvC2qq\
8gTeitcgOOHOroQkOUG4lK113g4wK4FcR2SqwbRrHr9OX679LIkSypOOZUVdloS+NEBa6wTQmQm2\
2blmc9Vg3UOS6wVt9ACd16BzcxM5u1mDueaWhT8xvuEv7MrGjrTHFt4OFFg=";

    let cert_der = base64::engine::general_purpose::STANDARD
        .decode(cert_base64)
        .expect("failed to decode certificate base64");

    let priv_key_der = base64::engine::general_purpose::STANDARD
        .decode(TEST_RSA_2048_PKCS8_DER_B64)
        .expect("failed to decode private key base64");

    let priv_key = RsaPrivateKey::from_pkcs8_der(&priv_key_der).expect("failed to parse key");
    let pub_key = priv_key.to_public_key();
    let pub_key_der = pub_key.to_public_key_der().expect("failed to encode public key").to_vec();

    let entry_id = "test-log-entry";

    // 1. Construct the PublicEndorsement
    let mut public_endorsement = PublicEndorsement {
        name: "endorsements/test".to_string(),
        statement: Some(Statement {
            format: StatementFormat::JsonIntoto.into(),
            serialized: endorsement_bytes.to_vec(),
        }),
        statement_signature: Some(Signature {
            signature: vec![0; 64],
            verification_material: Some(VerificationMaterial {
                verification_material: Some(VmOneof::EcdsaP256Sha256(EcdsaP256PublicKey {
                    der_bytes: dummy_endorser_key_bytes.clone(),
                })),
            }),
            time_stamp_token: vec![],
        }),
        endorsement_signatures: vec![Signature {
            signature: vec![],
            verification_material: Some(VerificationMaterial {
                verification_material: Some(VmOneof::X509Certificate(X509Der {
                    der_bytes: cert_der,
                })),
            }),
            time_stamp_token: vec![],
        }],
        tlog_receipt: Some(TLogReceipt { entry_id: entry_id.to_string() }),
    };

    // 2. Calculate PAE for signing
    let pae =
        crate::pae::calculate(endorsement_bytes, &dummy_endorser_key_bytes, &[0; 64], entry_id);

    // 3. Sign the PAE
    let mut hasher = Sha256Hasher::new();
    hasher.update(&pae);
    let hashed = hasher.finalize();
    let signature =
        priv_key.sign(Pkcs1v15Sign::new::<Sha256Hasher>(), &hashed).expect("failed to sign");

    // 4. Update the endorsement with the real signature
    public_endorsement.endorsement_signatures[0].signature = signature;

    use base64::engine::general_purpose::STANDARD;
    let pes_confirmation_json = serde_json::json!({
        "name": public_endorsement.name,
        "statement": {
            "serialized": STANDARD.encode(public_endorsement.statement.as_ref().unwrap().serialized.as_slice()),
            "format": "JSON_INTOTO",
        },
        "statementSignature": {
            "signature": STANDARD.encode(public_endorsement.statement_signature.as_ref().unwrap().signature.as_slice()),
            "verificationMaterial": {
                "ecdsaP256Sha256": {
                    "derBytes": STANDARD.encode(match public_endorsement.statement_signature.as_ref().unwrap().verification_material.as_ref().unwrap().verification_material.as_ref().unwrap() {
                        VmOneof::EcdsaP256Sha256(key) => &key.der_bytes,
                        _ => panic!("unexpected VM"),
                    }),
                }
            }
        },
        "endorsementSignatures": [
            {
                "signature": STANDARD.encode(public_endorsement.endorsement_signatures[0].signature.as_slice()),
                "verificationMaterial": {
                    "x509Certificate": {
                        "derBytes": STANDARD.encode(match public_endorsement.endorsement_signatures[0].verification_material.as_ref().unwrap().verification_material.as_ref().unwrap() {
                            VmOneof::X509Certificate(cert) => &cert.der_bytes,
                            _ => panic!("unexpected VM"),
                        }),
                    }
                }
            }
        ],
        "tlogReceipt": {
            "entryId": public_endorsement.tlog_receipt.as_ref().unwrap().entry_id,
        }
    });
    let pes_confirmation_bytes =
        serde_json::to_vec(&pes_confirmation_json).expect("failed to encode JSON");

    // 5. Setup trusted keys (Reference Value)
    let pes_key_set = VerifyingKeySet {
        keys: vec![VerifyingKey {
            r#type: KeyType::RsaSha2256.into(),
            key_id: 0,
            raw: pub_key_der,
        }],
        ..Default::default()
    };

    let trusted_endorser_key = VerifyingKey {
        r#type: KeyType::EcdsaP256Sha256.into(),
        key_id: 4711,
        raw: dummy_endorser_key_bytes.clone(),
    };

    (pes_confirmation_bytes, pes_key_set, trusted_endorser_key)
}

#[test]
fn test_verify_pes_confirmation_success() {
    let endorsement_bytes = b"{\"artifact\":\"test\"}";
    let (pes_confirmation_bytes, pes_key_set, trusted_endorser_key) =
        create_test_pes_confirmation_bytes(endorsement_bytes);
    // 6. Verify!
    let result = verify_pes_confirmation(
        &pes_confirmation_bytes,
        &pes_key_set,
        endorsement_bytes,
        Some(&trusted_endorser_key),
    );
    assert!(result.is_ok(), "Verification failed: {:?}", result.err());
}

fn untrusted_pes_signature_json() -> serde_json::Value {
    let fixture: serde_json::Value =
        serde_json::from_slice(include_bytes!("testdata/pes_confirmation.json")).unwrap();
    fixture["endorsementSignatures"][0].clone()
}

fn corrupted_pes_signature_json(valid_sig_json: &serde_json::Value) -> serde_json::Value {
    use base64::{Engine as _, engine::general_purpose::STANDARD};
    let mut corrupted = valid_sig_json.clone();
    corrupted["signature"] = serde_json::Value::String(STANDARD.encode(vec![0u8; 256]));
    corrupted
}

fn rewrite_endorsement_signatures(
    pes_confirmation_bytes: &[u8],
    signatures: Vec<serde_json::Value>,
) -> Vec<u8> {
    let mut json_val: serde_json::Value = serde_json::from_slice(pes_confirmation_bytes).unwrap();
    json_val["endorsementSignatures"] = serde_json::Value::Array(signatures);
    serde_json::to_vec(&json_val).unwrap()
}

#[test]
fn test_verify_pes_confirmation_multiple_signatures_first_valid_second_untrusted() {
    let endorsement_bytes = b"{\"artifact\":\"test\"}";
    let (pes_confirmation_bytes, pes_key_set, trusted_endorser_key) =
        create_test_pes_confirmation_bytes(endorsement_bytes);
    let base_json: serde_json::Value = serde_json::from_slice(&pes_confirmation_bytes).unwrap();
    let valid_sig = base_json["endorsementSignatures"][0].clone();
    let untrusted_sig = untrusted_pes_signature_json();

    let dual_signed_bytes =
        rewrite_endorsement_signatures(&pes_confirmation_bytes, vec![valid_sig, untrusted_sig]);

    let result = verify_pes_confirmation(
        &dual_signed_bytes,
        &pes_key_set,
        endorsement_bytes,
        Some(&trusted_endorser_key),
    );
    assert!(result.is_ok(), "Verification failed: {:?}", result.err());
}

#[test]
fn test_verify_pes_confirmation_multiple_signatures_first_untrusted_second_valid() {
    // Simulates PES key rotation after the older key is retired from
    // `pes_key_set`: the first signature in `endorsementSignatures` was
    // produced by the retired key, while the second signature was produced by
    // the active trusted key (b/556647889).
    let endorsement_bytes = b"{\"artifact\":\"test\"}";
    let (pes_confirmation_bytes, pes_key_set, trusted_endorser_key) =
        create_test_pes_confirmation_bytes(endorsement_bytes);
    let base_json: serde_json::Value = serde_json::from_slice(&pes_confirmation_bytes).unwrap();
    let valid_sig = base_json["endorsementSignatures"][0].clone();
    let untrusted_sig = untrusted_pes_signature_json();

    let dual_signed_bytes =
        rewrite_endorsement_signatures(&pes_confirmation_bytes, vec![untrusted_sig, valid_sig]);

    let result = verify_pes_confirmation(
        &dual_signed_bytes,
        &pes_key_set,
        endorsement_bytes,
        Some(&trusted_endorser_key),
    );
    assert!(result.is_ok(), "Verification failed: {:?}", result.err());
}

#[test]
fn test_verify_pes_confirmation_multiple_signatures_first_corrupted_second_valid() {
    let endorsement_bytes = b"{\"artifact\":\"test\"}";
    let (pes_confirmation_bytes, pes_key_set, trusted_endorser_key) =
        create_test_pes_confirmation_bytes(endorsement_bytes);
    let base_json: serde_json::Value = serde_json::from_slice(&pes_confirmation_bytes).unwrap();
    let valid_sig = base_json["endorsementSignatures"][0].clone();
    let corrupted_sig = corrupted_pes_signature_json(&valid_sig);

    let dual_signed_bytes =
        rewrite_endorsement_signatures(&pes_confirmation_bytes, vec![corrupted_sig, valid_sig]);

    let result = verify_pes_confirmation(
        &dual_signed_bytes,
        &pes_key_set,
        endorsement_bytes,
        Some(&trusted_endorser_key),
    );
    assert!(result.is_ok(), "Verification failed: {:?}", result.err());
}

#[test]
fn test_verify_pes_confirmation_multiple_signatures_and_multiple_keys_in_key_set() {
    let endorsement_bytes = b"{\"artifact\":\"test\"}";
    let (pes_confirmation_bytes, mut pes_key_set, trusted_endorser_key) =
        create_test_pes_confirmation_bytes(endorsement_bytes);
    let base_json: serde_json::Value = serde_json::from_slice(&pes_confirmation_bytes).unwrap();
    let valid_sig = base_json["endorsementSignatures"][0].clone();
    let untrusted_sig = untrusted_pes_signature_json();

    // Place a non-matching key at index 0 so the matching key is at index 1 of
    // `pes_key_set.keys`.
    pes_key_set.keys.insert(
        0,
        VerifyingKey {
            r#type: KeyType::EcdsaP256Sha256.into(),
            key_id: 99,
            raw: trusted_endorser_key.raw.clone(),
        },
    );

    let dual_signed_bytes =
        rewrite_endorsement_signatures(&pes_confirmation_bytes, vec![untrusted_sig, valid_sig]);

    let result = verify_pes_confirmation(
        &dual_signed_bytes,
        &pes_key_set,
        endorsement_bytes,
        Some(&trusted_endorser_key),
    );
    assert!(result.is_ok(), "Verification failed: {:?}", result.err());
}

#[test]
fn test_verify_pes_confirmation_multiple_signatures_all_invalid_fails() {
    let endorsement_bytes = b"{\"artifact\":\"test\"}";
    let (pes_confirmation_bytes, pes_key_set, trusted_endorser_key) =
        create_test_pes_confirmation_bytes(endorsement_bytes);
    let base_json: serde_json::Value = serde_json::from_slice(&pes_confirmation_bytes).unwrap();
    let valid_sig = base_json["endorsementSignatures"][0].clone();
    let untrusted_sig = untrusted_pes_signature_json();
    let corrupted_sig = corrupted_pes_signature_json(&valid_sig);

    let invalid_bytes =
        rewrite_endorsement_signatures(&pes_confirmation_bytes, vec![untrusted_sig, corrupted_sig]);

    let result = verify_pes_confirmation(
        &invalid_bytes,
        &pes_key_set,
        endorsement_bytes,
        Some(&trusted_endorser_key),
    );
    assert!(result.is_err());
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("signature[0]") && err_msg.contains("signature[1]"),
        "expected error details for all attempted signatures, got: {err_msg}"
    );
}

#[test]
fn test_verify_pes_confirmation_empty_signatures_fails() {
    let endorsement_bytes = b"{\"artifact\":\"test\"}";
    let (pes_confirmation_bytes, pes_key_set, trusted_endorser_key) =
        create_test_pes_confirmation_bytes(endorsement_bytes);
    let empty_sig_bytes = rewrite_endorsement_signatures(&pes_confirmation_bytes, vec![]);

    let result = verify_pes_confirmation(
        &empty_sig_bytes,
        &pes_key_set,
        endorsement_bytes,
        Some(&trusted_endorser_key),
    );
    assert!(result.is_err());
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("no endorsement signatures found"),
        "expected 'no endorsement signatures found', got: {err_msg}"
    );
}

fn make_test_endorsement_statement() -> Vec<u8> {
    let mut statement = intoto::statement::make_statement(
        "test-subject",
        &HexDigest {
            sha2_256: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
                .to_string(),
            ..Default::default()
        },
        Instant::from_unix_millis(1000),
        Instant::from_unix_millis(0),
        Instant::from_unix_millis(2000),
        vec![],
    );
    let mut publisher_annotations = alloc::collections::BTreeMap::new();
    publisher_annotations
        .insert("publisher_id".to_string(), "test-publisher@google.com".to_string());
    statement.predicate.claims.push(intoto::statement::Claim {
        r#type:
            "https://github.com/private-compute-infra-toolkit/public-endorsement-service/blob/main/docs/claims/publisher.md"
                .to_string(),
        annotations: publisher_annotations,
    });
    serde_json::to_vec(&statement).unwrap()
}

#[test]
fn test_verify_pes_endorsement_success() {
    let endorsement_bytes = make_test_endorsement_statement();
    let (pes_confirmation_bytes, pes_key_set, _) =
        create_test_pes_confirmation_bytes(&endorsement_bytes);

    let endorsement = Endorsement {
        format: EndorsementFormat::EndorsementFormatJsonIntoto.into(),
        serialized: endorsement_bytes,
        subject: vec![],
    };
    let ref_value = PesEndorsementReferenceValue {
        key_set: Some(pes_key_set),
        publisher_id: "test-publisher@google.com".to_string(),
        ..Default::default()
    };

    let result = verify_pes_endorsement(
        Instant::from_unix_millis(1000),
        &endorsement,
        &pes_confirmation_bytes,
        &ref_value,
    );
    assert!(result.is_ok(), "verify_pes_endorsement failed: {:?}", result.err());
}

#[test]
fn test_verify_pes_endorsement_failure_wrong_publisher() {
    let endorsement_bytes = make_test_endorsement_statement();
    let (pes_confirmation_bytes, pes_key_set, _) =
        create_test_pes_confirmation_bytes(&endorsement_bytes);

    let endorsement = Endorsement {
        format: EndorsementFormat::EndorsementFormatJsonIntoto.into(),
        serialized: endorsement_bytes,
        subject: vec![],
    };
    let ref_value = PesEndorsementReferenceValue {
        key_set: Some(pes_key_set),
        publisher_id: "wrong-publisher@google.com".to_string(),
        ..Default::default()
    };

    let result = verify_pes_endorsement(
        Instant::from_unix_millis(1000),
        &endorsement,
        &pes_confirmation_bytes,
        &ref_value,
    );
    assert!(result.is_err());
}

#[test]
fn test_verify_pes_endorsement_failure_missing_required_claim() {
    let endorsement_bytes = make_test_endorsement_statement();
    let (pes_confirmation_bytes, pes_key_set, _) =
        create_test_pes_confirmation_bytes(&endorsement_bytes);

    let endorsement = Endorsement {
        format: EndorsementFormat::EndorsementFormatJsonIntoto.into(),
        serialized: endorsement_bytes,
        subject: vec![],
    };
    let req_claims = ClaimReferenceValue {
        claims: vec![Claim {
            r#type: "https://example.com/missing_claim".to_string(),
            annotations: Default::default(),
        }],
        ..Default::default()
    };
    let ref_value = PesEndorsementReferenceValue {
        key_set: Some(pes_key_set),
        publisher_id: "test-publisher@google.com".to_string(),
        additional_required_claims: Some(req_claims),
        ..Default::default()
    };

    let result = verify_pes_endorsement(
        Instant::from_unix_millis(1000),
        &endorsement,
        &pes_confirmation_bytes,
        &ref_value,
    );
    assert!(result.is_err());
}

#[test]
#[allow(deprecated)]
fn test_verify_pes_endorsement_failure_missing_required_claim_type() {
    let endorsement_bytes = make_test_endorsement_statement();
    let (pes_confirmation_bytes, pes_key_set, _) =
        create_test_pes_confirmation_bytes(&endorsement_bytes);

    let endorsement = Endorsement {
        format: EndorsementFormat::EndorsementFormatJsonIntoto.into(),
        serialized: endorsement_bytes,
        subject: vec![],
    };
    let req_claims = ClaimReferenceValue {
        claim_types: vec!["https://example.com/missing_claim".to_string()],
        ..Default::default()
    };
    let ref_value = PesEndorsementReferenceValue {
        key_set: Some(pes_key_set),
        publisher_id: "test-publisher@google.com".to_string(),
        additional_required_claims: Some(req_claims),
        ..Default::default()
    };

    let result = verify_pes_endorsement(
        Instant::from_unix_millis(1000),
        &endorsement,
        &pes_confirmation_bytes,
        &ref_value,
    );
    assert!(result.is_err());
}

#[test]
fn test_verify_pes_endorsement_failure_publisher_id_in_additional_claims() {
    let endorsement_bytes = make_test_endorsement_statement();
    let (pes_confirmation_bytes, pes_key_set, _) =
        create_test_pes_confirmation_bytes(&endorsement_bytes);

    let endorsement = Endorsement {
        format: EndorsementFormat::EndorsementFormatJsonIntoto.into(),
        serialized: endorsement_bytes,
        subject: vec![],
    };
    let req_claims = ClaimReferenceValue {
        claims: vec![Claim {
            r#type: "https://github.com/private-compute-infra-toolkit/public-endorsement-service/blob/main/docs/claims/publisher.md".to_string(),
            annotations: Default::default(),
        }],
        ..Default::default()
    };
    let ref_value = PesEndorsementReferenceValue {
        key_set: Some(pes_key_set),
        publisher_id: "test-publisher@google.com".to_string(),
        additional_required_claims: Some(req_claims),
        ..Default::default()
    };

    let result = verify_pes_endorsement(
        Instant::from_unix_millis(1000),
        &endorsement,
        &pes_confirmation_bytes,
        &ref_value,
    );
    assert!(result.is_err());
    assert!(
        result.unwrap_err().to_string().contains("invalid argument"),
        "expected error to contain invalid argument"
    );
}

#[test]
fn test_parse_pes_confirmation_json_file() {
    let pes_confirmation_bytes = include_bytes!("testdata/pes_confirmation.json");
    let public_endorsement_result = crate::parse_pes_confirmation(pes_confirmation_bytes);

    assert!(
        public_endorsement_result.is_ok(),
        "Failed to parse PES confirmation: {:?}",
        public_endorsement_result.err()
    );
    let pe = public_endorsement_result.unwrap();
    assert_eq!(pe.name, "endorsements/1018802f-d7ce-48a1-84df-0fe0abc497dd");

    // Helper to easily get expected bytes in tests
    use base64::{Engine as _, engine::general_purpose::STANDARD};

    // Assert statement
    let statement = pe.statement.expect("statement should be present");
    assert_eq!(statement.format, StatementFormat::JsonIntoto as i32);
    let expected_serialized = STANDARD.decode("ewogICJfdHlwZSI6ICJodHRwczovL2luLXRvdG8uaW8vU3RhdGVtZW50L3YxIiwKICAicHJlZGljYXRlVHlwZSI6ICJodHRwczovL3Byb2plY3Qtb2FrLmdpdGh1Yi5pby9vYWsvdHIvZW5kb3JzZW1lbnQvdjEiLAogICJzdWJqZWN0IjogWwogICAgewogICAgICAibmFtZSI6ICJvYWtfdGNhX3Nka190ZXN0X3RydXN0ZWRfYXBwIiwKICAgICAgImRpZ2VzdCI6IHsKICAgICAgICAic2hhMjU2IjogIjY2Y2ZjNTMyNTI5YTY4NThmYjg5ZjdjMmM3MTk2NWM3YjNkOTIyNTQxMzQ4Nzg3OTRlZWFiZDRmZWI3NTNhMWYiCiAgICAgIH0KICAgIH0KICBdLAogICJwcmVkaWNhdGUiOiB7CiAgICAiaXNzdWVkT24iOiAiMjAyNi0wNS0wNlQwODoxODowOC4zNzMwMDBaIiwKICAgICJ2YWxpZGl0eSI6IHsKICAgICAgIm5vdEJlZm9yZSI6ICIyMDI2LTA1LTA2VDA4OjE4OjA4LjM3MzAwMFoiLAogICAgICAibm90QWZ0ZXIiOiAiMjAyNi0wOC0wNFQwODoxODowOC4zNzMwMDBaIgogICAgfSwKICAgICJjbGFpbXMiOiBbCiAgICAgIHsKICAgICAgICAidHlwZSI6ICJodHRwczovL2dpdGh1Yi5jb20vcGNpdC9wZXMvZG9jcy9jbGFpbXMvdjEvcHVibGlzaGVyLm1kIiwKICAgICAgICAiYW5ub3RhdGlvbnMiOiB7CiAgICAgICAgICAicHVibGlzaGVyX2lkIjogInBjaXQtcmVsZWFzZS1ib3RAZ29vZ2xlLmNvbSIKICAgICAgICB9CiAgICAgIH0sCiAgICAgIHsKICAgICAgICAidHlwZSI6ICJodHRwczovL2dpdGh1Yi5jb20vcGNpdC9wZXMvZG9jcy9jbGFpbXMvdjEvd29ya2xvYWQubWQiLAogICAgICAgICJhbm5vdGF0aW9ucyI6IHsKICAgICAgICAgICJ3b3JrbG9hZF9pZCI6ICJvYWtfdGNhX3Nka190ZXN0X3RydXN0ZWRfYXBwIiwKICAgICAgICAgICJ2ZXJzaW9uIjogIjEuMC4wIgogICAgICAgIH0KICAgICAgfQogICAgXQogIH0KfQo=").unwrap();
    assert_eq!(statement.serialized, expected_serialized);

    // Assert statement signature
    let statement_signature =
        pe.statement_signature.expect("statement_signature should be present");
    let expected_stmt_sig = STANDARD.decode("MEYCIQCS5E5MvSCQsgyj7p85jkdNy9AaUbYuvTnkmJeqPSbW1gIhALWiQaMMan63FSIvMl2uoTzQ9SfHvY3BhfPbyYDApS5m").unwrap();
    assert_eq!(statement_signature.signature, expected_stmt_sig);

    let stmt_vm = statement_signature
        .verification_material
        .expect("statement signature should have verification material");
    let expected_ecdsa_der = STANDARD.decode("MFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAESKycnwFAxon7f2cBEqpK2foeJntrnkNWMCCGLVfGCfOCUi81P3EZT2KUl8OzMXZdwpGqkoLYa1EWcYwykeA52A==").unwrap();
    if let Some(VmOneof::EcdsaP256Sha256(key)) = stmt_vm.verification_material {
        assert_eq!(key.der_bytes, expected_ecdsa_der);
    } else {
        panic!("statement verification material should be EcdsaP256Sha256");
    }

    // Assert endorsement signatures
    assert_eq!(pe.endorsement_signatures.len(), 1);
    let end_sig = &pe.endorsement_signatures[0];
    let expected_end_sig = STANDARD.decode("rxLU/UUOA5X/5JCYZZZg2OdcZxA2KlG/0jE4lXyGTej4o1PRH04JAALulzUS19PbJcRkq8CygrW8Izpz5xo8i3BqjNlksrNdxFOUQcmBMr4iXTT5Je3rNgH3TDZvBc61xDzaIUYWNMPrnlpaE17Eivxelew/YwXyWdNsC+GsaIDEQRN9+iPj1COpehfZri5keq43b/PYdwUCL246jfNUwdaC/Bbhmf3GKhKrJ8spw2miHOaZbGoJ4BHXrY8zWjwrzASBwL4cjeBsoYiTcSmbBvTGCtxJB8raTkJQkjRbfUYmpdtvco07yzle+T0T/9CTZPzaZMJ/Xcee6KjFgvVbQsPkyjxWM4I4TGmE+aHbxI3Fdwwix19sgjRh0fVVYJKGdFObyCpubJ3VIei952TEyExUsE11Pse37VmlPdaM+pHuFybKWQMjbANZbdiiX1sXZT7DfLD+FLZ305BWi5MXOARRTNecVk8QtK4nI80vni8KixNttyiLr69Nwz6aIgRlBsr2O6u0yA7ix0uPlt13PUKGE6GuxCPgKv7AyA2RYnqFowNnzsdoTBk7HR/GmgxaCWWYt4klfSsx0Gyh+ygSdRQGEWDYxvyVB3CC96N8g8b29i1aVaRqZ4vTh/1H5FylYj0g7oe/+/BUQT+4qBSD2ECpuoXTVdSqAnwDCBmbvfs=").unwrap();
    assert_eq!(end_sig.signature, expected_end_sig);

    let end_vm = end_sig
        .verification_material
        .as_ref()
        .expect("endorsement signature should have verification material");
    let expected_x509_der = STANDARD.decode("MIIEyjCCArKgAwIBAgIUaqEOQS1k8/8LCR+S4LZmHNJCzswwDQYJKoZIhvcNAQELBQAwDjEMMAoGA1UEAwwDUEVTMB4XDTI2MDQyNjEzNTMwNVoXDTI2MDgyNTEzNTMwNVowDjEMMAoGA1UEAwwDUEVTMIICIjANBgkqhkiG9w0BAQEFAAOCAg8AMIICCgKCAgEA4iCEMhRhaEDNSmo77m5dJ6ZXJlRbL0Jv7ptCmPv6sqFf12AADjASlVlswFy/Nui9bjOsI432YRiamGhcprypkDkrWI7KmhzLrgxIeBiElKe/kJ7wc6m9oKkRJgeMZkXZmKPDfTWouF52EuUWxx9XTpW1UMEhkh8Z9hYUpkx8vgLnx7FLqSJGVS470jRcBZu32yetN6yZkAxtM/1DhoBysVSd7R/JYhsrwvsRHo3Tkg824qwAXR/yUmMM3pc4nakNGVMEkom4jYbbZ5d//ENJwG6j+AXR516XV3ehxCNX4baEkwJfTUaJsa9T3RaPLyRArtKgjWkUnryKZQmn4APo8doexk0KZAaQiRfc2VJib0nWaA+Jqfj73Pjksr5hxCsw6fjnXNctoRr9L/E+PaXcGWEu9O+NPeBmFeM/NpR9mnbLmjAInsGYxW8+jI/yByl65bKwdOkVAVwI2W4XHJqojjWB2dgy9r4ShKxyKlbA2ApUKXOKhChCTv3iSDW7xgucYUjeY+Zb4afLShpiXSjpn3jdD4kjnkKE5pVwCtwhaQ9nwT8Zl0tGtQyCRfkG2o/Xmn5YHWA0gNaEsEF68i+MaI9oic/LvaccuchcO7JVXpgNRUh4+oJSnAhe5ggQ2/DrdGUF+r3QrPQu3y3ra+XSH6l7obMXJhn5k+FhoqUAa0MCAwEAAaMgMB4wDAYDVR0TAQH/BAIwADAOBgNVHQ8BAf8EBAMCB4AwDQYJKoZIhvcNAQELBQADggIBAK1AX4HoWxZbMqAg8tYK0hh0nvFQsOC2+Q4W9uPKHTdAdEt+kl9GwWia6zY5MP5YVqnDEigINWP3qeGP151VrJ/1x74CxxpEpOido+VlDdWUWYwDs9VcYNy6CrN9vp5bHoMUJo9C8ef5jyfytMpLXpYu5VOqkfjELjNItS7IMbuqR3JJGX1WxIS+rOPVp7VRts39xRfyZfxdKoGbRkGn9DnVEONcJYxvpBJkCNsSxVI+LwOyMDzBbQJXwmgl1zAI1FoTyUkvqpC5asTC3vVczhmYCNMKagkTmYOepwevRDVicOPCPs+6Ign90sL2MEan/uIUMdu3OQ0cVdkxchuItAzvIxVbsdRY0kce+RXTshQswTIS2CL52TJkEZfqOBtjCOFIez+CDHhFF0ATTMGuMRy4ZRKgD7M5A6Go1b9ng46GsHckt44Q5OQjswFCJIqePotU3fpncdtjQL7Fj3ujYzia6J6aSjHOImvrDQ/WGAFBmcVSBbFL2zAQNb01/egVQE9ykngFts1K4jOu49SUojZeJRfAR3ZTBdqI4JxLjROJCJk8tGg9MfdOdtBqb7VmF5g6R8QkhqCKdI5ugDVTYhAVqb3CWXe3vvvQDBmcsHKS1KRrYX3uPmkPOM6Fn9wNtkR3OhLm0YRBpLKR0pFHHBQfSqI1Cr45GyBXc74FSzti").unwrap();
    if let Some(VmOneof::X509Certificate(cert)) = &end_vm.verification_material {
        assert_eq!(cert.der_bytes, expected_x509_der);
    } else {
        panic!("endorsement verification material should be X509Certificate");
    }

    // Assert tlog receipt
    let tlog_receipt = pe.tlog_receipt.expect("tlog_receipt should be present");
    assert_eq!(
        tlog_receipt.entry_id,
        "entries/1b71272824ca62894647e6c009304f4d7366b7d9026b652791581a11dc8c4beb_afad48fc-5056-4cd9-b2ec-b11f1976f249"
    );
}

#[test]
fn test_parse_tsa_root_certs() {
    let empty: &[Vec<u8>] = &[];
    assert!(time_stamp_token::parse_tsa_root_certs(empty).unwrap().is_empty());

    let token_der = time_stamp_token::verification_tests::load_globalsign_token_der();
    let content_info =
        time_stamp_token::ContentInfo::from_der(&token_der).expect("should parse ContentInfo");
    let signed_data = content_info
        .content
        .decode_as::<time_stamp_token::SignedData<'_>>()
        .expect("should parse SignedData");
    let certs = signed_data.certificates.expect("expected certificates");
    // The certificates embedded in the token are not actually root CA
    // certificates, but they are valid X.509 certificates and therefore
    // sufficient for testing DER certificate parsing.
    let cert0 = &certs[0];
    let cert1 = &certs[1];
    let cert0_der = cert0.to_der().expect("should encode first cert");
    let cert1_der = cert1.to_der().expect("should encode second cert");

    let parsed = time_stamp_token::parse_tsa_root_certs(core::slice::from_ref(&cert0_der))
        .expect("should parse DER cert");
    assert_eq!(parsed, vec![cert0.clone()]);

    let parsed_multiple = time_stamp_token::parse_tsa_root_certs(&[cert0_der, cert1_der])
        .expect("should parse multiple DER certs");
    assert_eq!(parsed_multiple, vec![cert0.clone(), cert1.clone()]);

    let invalid = time_stamp_token::parse_tsa_root_certs(&[b"not valid der".to_vec()]);
    assert!(matches!(invalid, Err(time_stamp_token::TimeStampTokenError::Der(_))));
}

struct TestPki {
    root_cert: x509_cert::Certificate,
    intermediate_cert: x509_cert::Certificate,
    signer_cert: x509_cert::Certificate,
    signer_key: p256::ecdsa::SigningKey,
}

fn build_test_tsa_pki() -> TestPki {
    use oak_time::make_instant;
    use x509_cert::{Version, der::asn1::OctetString, ext::pkix::SubjectKeyIdentifier};

    use crate::time_stamp_token::chain_tests::{
        CertSpec, build_cert, default_ca_extensions, default_signer_extensions, make_ext, p256_key,
    };

    let root_key = p256_key(0x11);
    let interm_key = p256_key(0x22);
    let signer_key = p256_key(0x33);

    let root_cert = build_cert(&CertSpec {
        version: Version::V3,
        serial: 1,
        issuer_cn: "Test TSA Root CA",
        subject_cn: "Test TSA Root CA",
        not_before: make_instant!("2020-01-01T00:00:00Z"),
        not_after: make_instant!("2035-01-01T00:00:00Z"),
        subject_key: &root_key,
        issuer_key: &root_key,
        extensions: default_ca_extensions(None),
    });

    let intermediate_cert = build_cert(&CertSpec {
        version: Version::V3,
        serial: 2,
        issuer_cn: "Test TSA Root CA",
        subject_cn: "Test TSA Intermediate CA",
        not_before: make_instant!("2024-01-01T00:00:00Z"),
        not_after: make_instant!("2030-01-01T00:00:00Z"),
        subject_key: &interm_key,
        issuer_key: &root_key,
        extensions: default_ca_extensions(None),
    });

    let mut signer_exts = default_signer_extensions();
    signer_exts.push(make_ext(
        false,
        &SubjectKeyIdentifier(OctetString::new([0xAA, 0xBB, 0xCC, 0xDD]).unwrap()),
    ));
    let signer_cert = build_cert(&CertSpec {
        version: Version::V3,
        serial: 3,
        issuer_cn: "Test TSA Intermediate CA",
        subject_cn: "Test TSA Signer",
        not_before: make_instant!("2026-01-01T00:00:00Z"),
        not_after: make_instant!("2028-01-01T00:00:00Z"),
        subject_key: &signer_key,
        issuer_key: &interm_key,
        extensions: signer_exts,
    });

    TestPki { root_cert, intermediate_cert, signer_cert, signer_key }
}

fn create_test_pes_sig_and_cert() -> (Vec<u8>, x509_cert::Certificate) {
    let (pes_confirmation_bytes, _, _) =
        create_test_pes_confirmation_bytes(b"{\"artifact\":\"test\"}");
    let pe = crate::parse_pes_confirmation(&pes_confirmation_bytes).unwrap();
    let pes_sig = &pe.endorsement_signatures[0];
    let cert_der =
        crate::extract_raw_vm_bytes(pes_sig.verification_material.as_ref().unwrap()).unwrap();
    let pes_cert = x509_cert::Certificate::from_der(cert_der).unwrap();
    (pes_sig.signature.clone(), pes_cert)
}

fn build_test_time_stamp_token_der(
    pes_signature: &[u8],
    gen_time: Instant,
    certs: &[&x509_cert::Certificate],
    signer_issuer_cn: &str,
    signer_serial: u32,
    use_ski_sid: Option<&[u8]>,
    signer_key: &p256::ecdsa::SigningKey,
) -> Vec<u8> {
    use const_oid::{
        ObjectIdentifier,
        db::{
            rfc4519::CN,
            rfc5911::{ID_CONTENT_TYPE, ID_MESSAGE_DIGEST},
            rfc5912::{ECDSA_WITH_SHA_256, ID_SHA_256, ID_SHA_384},
        },
    };
    use oak_digest::{Sha256, Sha384};
    use p256::ecdsa::signature::Signer;
    use x509_cert::{
        attr::{AttributeTypeAndValue, Attributes},
        der::{
            Any,
            asn1::{OctetString, OctetStringRef, SetOfVec, Utf8StringRef},
        },
        name::{RdnSequence, RelativeDistinguishedName},
        serial_number::SerialNumber,
        spki::AlgorithmIdentifierOwned,
    };

    use crate::time_stamp_token::verification_tests::{encode_signed_data, make_attr};

    // 1. Build TSTInfo (using SHA-384 for messageImprint like PES SimpleTsaClient).
    let imprint_hash = Sha384::from_contents(pes_signature);
    let tst_info = time_stamp_token::TstInfo {
        version: 1,
        policy: ObjectIdentifier::new_unwrap("1.2.3.4.5"),
        message_imprint: time_stamp_token::MessageImprint {
            hash_algorithm: AlgorithmIdentifierOwned { oid: ID_SHA_384, parameters: None },
            hashed_message: OctetString::new(imprint_hash.as_ref()).unwrap(),
        },
        serial_number: SerialNumber::from(42u32),
        gen_time: time_stamp_token::Rfc3161GeneralizedTime(gen_time),
        accuracy: None,
        ordering: false,
        nonce: None,
        tsa: None,
        extensions: None,
    };
    let tst_info_der = tst_info.to_der().unwrap();

    // 2. Build SignedAttributes (content-type = id-ct-TSTInfo, message-digest =
    //    SHA-256(tst_info_der), id-aa-signingCertificateV2 = SHA-256(signer_cert)).
    let tst_digest = Sha256::from_contents(&tst_info_der);
    let signer_cert_der = certs[0].to_der().unwrap();
    let signer_cert_digest = Sha256::from_contents(&signer_cert_der);
    let signing_cert_v2 = time_stamp_token::SigningCertificateV2 {
        certs: vec![time_stamp_token::EssCertIdV2 {
            hash_algorithm: AlgorithmIdentifierOwned { oid: ID_SHA_256, parameters: None },
            cert_hash: OctetString::new(signer_cert_digest.as_ref()).unwrap(),
            issuer_serial: None,
        }],
        policies: None,
    };
    let signing_cert_v2_der = signing_cert_v2.to_der().unwrap();
    let mut signed_attrs = Attributes::new();
    signed_attrs
        .insert(make_attr(
            ID_CONTENT_TYPE,
            vec![Any::encode_from(&time_stamp_token::ID_CT_TST_INFO).unwrap()],
        ))
        .unwrap();
    signed_attrs
        .insert(make_attr(
            ID_MESSAGE_DIGEST,
            vec![Any::encode_from(&OctetString::new(tst_digest.as_ref()).unwrap()).unwrap()],
        ))
        .unwrap();
    signed_attrs
        .insert(make_attr(
            time_stamp_token::ID_AA_SIGNING_CERTIFICATE_V2,
            vec![Any::from_der(&signing_cert_v2_der).unwrap()],
        ))
        .unwrap();

    let signed_attrs_der = signed_attrs.to_der().unwrap();
    let cms_sig: p256::ecdsa::Signature = signer_key.sign(&signed_attrs_der);
    let cms_sig_der = cms_sig.to_der();

    // 3. Build SignerInfo.
    let (si_version, sid) = if let Some(ski_bytes) = use_ski_sid {
        (
            3,
            time_stamp_token::SignerIdentifier::SubjectKeyIdentifier(
                OctetString::new(ski_bytes).unwrap(),
            ),
        )
    } else {
        (
            1,
            time_stamp_token::SignerIdentifier::IssuerAndSerialNumber(
                time_stamp_token::IssuerAndSerialNumber {
                    issuer: RdnSequence(vec![RelativeDistinguishedName(
                        SetOfVec::try_from(vec![AttributeTypeAndValue {
                            oid: CN,
                            value: Any::from(Utf8StringRef::new(signer_issuer_cn).unwrap()),
                        }])
                        .unwrap(),
                    )]),
                    serial_number: SerialNumber::from(signer_serial),
                },
            ),
        )
    };

    let sha256_alg = AlgorithmIdentifierOwned { oid: ID_SHA_256, parameters: None };
    let signer_info = time_stamp_token::SignerInfo {
        version: si_version,
        sid,
        digest_algorithm: sha256_alg.clone(),
        signed_attrs: Some(signed_attrs),
        signature_algorithm: AlgorithmIdentifierOwned { oid: ECDSA_WITH_SHA_256, parameters: None },
        signature: OctetString::new(cms_sig_der.as_bytes()).unwrap(),
        unsigned_attrs: None,
    };

    // 4. Build SignedData and ContentInfo.
    let signed_data = time_stamp_token::SignedData {
        version: 3,
        digest_algorithms: SetOfVec::try_from(vec![sha256_alg]).unwrap(),
        encap_content_info: time_stamp_token::EncapsulatedContentInfo {
            econtent_type: time_stamp_token::ID_CT_TST_INFO,
            econtent: Some(OctetStringRef::new(&tst_info_der).unwrap()),
        },
        certificates: Some(certs.iter().map(|c| (*c).clone()).collect()),
        crls: None,
        signer_infos: SetOfVec::try_from(vec![signer_info]).unwrap(),
    };
    encode_signed_data(&signed_data)
}

#[test]
fn test_verify_time_stamp_token_subject_key_identifier_sid() {
    use oak_time::make_instant;
    use x509_cert::{Version, der::asn1::OctetString, ext::pkix::SubjectKeyIdentifier};

    use crate::time_stamp_token::{
        chain_tests::{CertSpec, build_cert, default_signer_extensions, make_ext, p256_key},
        verification_tests::encode_signed_data,
    };

    let (pes_signature, pes_cert) = create_test_pes_sig_and_cert();
    let pki = build_test_tsa_pki();

    let base_token_der = build_test_time_stamp_token_der(
        &pes_signature,
        make_instant!("2026-06-15T12:00:00Z"),
        &[&pki.signer_cert, &pki.intermediate_cert],
        "Test TSA Intermediate CA",
        3,
        Some(&[0xAA, 0xBB, 0xCC, 0xDD]),
        &pki.signer_key,
    );
    assert_eq!(
        time_stamp_token::verify_time_stamp_token(
            &base_token_der,
            &pes_signature,
            &pes_cert,
            core::slice::from_ref(&pki.root_cert),
        ),
        Ok(())
    );

    // Even when an older/expired TSA signer certificate sharing the same SKI
    // appears first in `SignedData.certificates`, SKI lookup tries all
    // matching candidates and succeeds on the renewed certificate bound by
    // `SigningCertificateV2`.
    let mut signer_exts = default_signer_extensions();
    signer_exts.push(make_ext(
        false,
        &SubjectKeyIdentifier(OctetString::new([0xAA, 0xBB, 0xCC, 0xDD]).unwrap()),
    ));
    let expired_same_ski_signer = build_cert(&CertSpec {
        version: Version::V3,
        serial: 29,
        issuer_cn: "Test TSA Intermediate CA",
        subject_cn: "Test TSA Signer",
        not_before: make_instant!("2024-01-01T00:00:00Z"),
        not_after: make_instant!("2025-01-01T00:00:00Z"),
        subject_key: &pki.signer_key,
        issuer_key: &p256_key(0x22),
        extensions: signer_exts,
    });
    let base_ci = time_stamp_token::ContentInfo::from_der(&base_token_der).unwrap();
    let mut sd = base_ci.content.decode_as::<time_stamp_token::SignedData<'_>>().unwrap();
    sd.certificates.as_mut().unwrap().insert(0, expired_same_ski_signer);
    let renewed_token_der = encode_signed_data(&sd);
    assert_eq!(
        time_stamp_token::verify_time_stamp_token(
            &renewed_token_der,
            &pes_signature,
            &pes_cert,
            core::slice::from_ref(&pki.root_cert),
        ),
        Ok(())
    );
}

#[test]
fn test_verify_time_stamp_token_fails_gen_time_before_pes_cert_validity() {
    use oak_time::make_instant;

    let (pes_signature, pes_cert) = create_test_pes_sig_and_cert();
    let pki = build_test_tsa_pki();
    // PES cert not_before is 2026-05-07T15:52:37Z; TSA certs are valid over
    // 2026..2028.
    let at_not_before = build_test_time_stamp_token_der(
        &pes_signature,
        make_instant!("2026-05-07T15:52:37Z"),
        &[&pki.signer_cert, &pki.intermediate_cert],
        "Test TSA Intermediate CA",
        3,
        None,
        &pki.signer_key,
    );
    assert_eq!(
        time_stamp_token::verify_time_stamp_token(
            &at_not_before,
            &pes_signature,
            &pes_cert,
            core::slice::from_ref(&pki.root_cert),
        ),
        Ok(())
    );

    for gen_time in
        [make_instant!("2026-05-07T15:52:36.999999999Z"), make_instant!("2026-02-01T00:00:00Z")]
    {
        let token_der = build_test_time_stamp_token_der(
            &pes_signature,
            gen_time,
            &[&pki.signer_cert, &pki.intermediate_cert],
            "Test TSA Intermediate CA",
            3,
            None,
            &pki.signer_key,
        );
        let res = time_stamp_token::verify_time_stamp_token(
            &token_der,
            &pes_signature,
            &pes_cert,
            core::slice::from_ref(&pki.root_cert),
        );
        assert_eq!(
            res,
            Err(time_stamp_token::TimeStampTokenError::IssuanceTimeOutsidePesCertValidity)
        );
    }
}

#[test]
fn test_verify_time_stamp_token_fails_gen_time_after_pes_cert_validity() {
    use oak_time::make_instant;

    let (pes_signature, pes_cert) = create_test_pes_sig_and_cert();
    let pki = build_test_tsa_pki();
    // PES cert not_after is 2027-05-07T15:52:37Z; TSA certs are valid over
    // 2026..2028.
    let at_not_after = build_test_time_stamp_token_der(
        &pes_signature,
        make_instant!("2027-05-07T15:52:37Z"),
        &[&pki.signer_cert, &pki.intermediate_cert],
        "Test TSA Intermediate CA",
        3,
        None,
        &pki.signer_key,
    );
    assert_eq!(
        time_stamp_token::verify_time_stamp_token(
            &at_not_after,
            &pes_signature,
            &pes_cert,
            core::slice::from_ref(&pki.root_cert),
        ),
        Ok(())
    );

    for gen_time in
        [make_instant!("2027-05-07T15:52:37.000000001Z"), make_instant!("2027-08-01T00:00:00Z")]
    {
        let token_der = build_test_time_stamp_token_der(
            &pes_signature,
            gen_time,
            &[&pki.signer_cert, &pki.intermediate_cert],
            "Test TSA Intermediate CA",
            3,
            None,
            &pki.signer_key,
        );
        let res = time_stamp_token::verify_time_stamp_token(
            &token_der,
            &pes_signature,
            &pes_cert,
            core::slice::from_ref(&pki.root_cert),
        );
        assert_eq!(
            res,
            Err(time_stamp_token::TimeStampTokenError::IssuanceTimeOutsidePesCertValidity)
        );
    }
}

#[test]
fn test_verify_time_stamp_token_fails_gen_time_outside_tsa_cert_validity() {
    use oak_time::make_instant;
    use x509_cert::Version;

    use crate::time_stamp_token::chain_tests::{
        CertSpec, build_cert, default_signer_extensions, p256_key,
    };

    let (pes_signature, pes_cert) = create_test_pes_sig_and_cert();
    let pki = build_test_tsa_pki();

    // Signer cert whose validity window (2026-06-01 .. 2026-07-01) lies
    // strictly inside PES cert validity (2026-05-07 .. 2027-05-07).
    let signer_cert = build_cert(&CertSpec {
        version: Version::V3,
        serial: 3,
        issuer_cn: "Test TSA Root CA",
        subject_cn: "Test TSA Signer",
        not_before: make_instant!("2026-06-01T00:00:00Z"),
        not_after: make_instant!("2026-07-01T00:00:00Z"),
        subject_key: &pki.signer_key,
        issuer_key: &p256_key(0x11),
        extensions: default_signer_extensions(),
    });

    for valid_gen_time in
        [make_instant!("2026-06-01T00:00:00Z"), make_instant!("2026-07-01T00:00:00Z")]
    {
        let valid_token_der = build_test_time_stamp_token_der(
            &pes_signature,
            valid_gen_time,
            &[&signer_cert],
            "Test TSA Root CA",
            3,
            None,
            &pki.signer_key,
        );
        assert_eq!(
            time_stamp_token::verify_time_stamp_token(
                &valid_token_der,
                &pes_signature,
                &pes_cert,
                core::slice::from_ref(&pki.root_cert),
            ),
            Ok(())
        );
    }

    for out_of_range_gen_time in [
        make_instant!("2026-05-31T23:59:59.999999999Z"),
        make_instant!("2026-07-01T00:00:00.000000001Z"),
    ] {
        let token_der = build_test_time_stamp_token_der(
            &pes_signature,
            out_of_range_gen_time,
            &[&signer_cert],
            "Test TSA Root CA",
            3,
            None,
            &pki.signer_key,
        );
        let res = time_stamp_token::verify_time_stamp_token(
            &token_der,
            &pes_signature,
            &pes_cert,
            core::slice::from_ref(&pki.root_cert),
        );
        assert_eq!(res, Err(time_stamp_token::TimeStampTokenError::CertificateValidityPeriod));
    }
}

#[test]
fn test_verify_time_stamp_token_fails_message_imprint_mismatch() {
    use oak_time::make_instant;

    let (pes_signature, pes_cert) = create_test_pes_sig_and_cert();
    let pki = build_test_tsa_pki();
    let other_sig = b"wrong signature bytes";
    let token_der = build_test_time_stamp_token_der(
        other_sig,
        make_instant!("2026-06-15T12:00:00Z"),
        &[&pki.signer_cert, &pki.intermediate_cert],
        "Test TSA Intermediate CA",
        3,
        None,
        &pki.signer_key,
    );

    assert_eq!(
        time_stamp_token::verify_time_stamp_token(
            &token_der,
            other_sig,
            &pes_cert,
            core::slice::from_ref(&pki.root_cert),
        ),
        Ok(())
    );

    let res = time_stamp_token::verify_time_stamp_token(
        &token_der,
        &pes_signature,
        &pes_cert,
        core::slice::from_ref(&pki.root_cert),
    );
    assert_eq!(res, Err(time_stamp_token::TimeStampTokenError::MessageImprintMismatch));
}

#[test]
fn test_verify_time_stamp_token_fails_invalid_cms_signature() {
    use oak_time::make_instant;

    use crate::time_stamp_token::chain_tests::p256_key;

    let (pes_signature, pes_cert) = create_test_pes_sig_and_cert();
    let pki = build_test_tsa_pki();

    let token_der = build_test_time_stamp_token_der(
        &pes_signature,
        make_instant!("2026-06-15T12:00:00Z"),
        &[&pki.signer_cert, &pki.intermediate_cert],
        "Test TSA Intermediate CA",
        3,
        None,
        &p256_key(0x99),
    );

    let res = time_stamp_token::verify_time_stamp_token(
        &token_der,
        &pes_signature,
        &pes_cert,
        core::slice::from_ref(&pki.root_cert),
    );
    assert!(matches!(res, Err(time_stamp_token::TimeStampTokenError::SignatureVerification(_))));
}

#[test]
fn test_verify_time_stamp_token_fails_mismatched_signing_certificate_v2() {
    use oak_time::make_instant;

    let (pes_signature, pes_cert) = create_test_pes_sig_and_cert();
    let pki = build_test_tsa_pki();
    // Put intermediate_cert first so build_test_time_stamp_token_der hashes the
    // wrong certificate into SigningCertificateV2 while SignerIdentifier still
    // selects signer_cert (serial 3).
    let token_der = build_test_time_stamp_token_der(
        &pes_signature,
        make_instant!("2026-06-15T12:00:00Z"),
        &[&pki.intermediate_cert, &pki.signer_cert],
        "Test TSA Intermediate CA",
        3,
        None,
        &pki.signer_key,
    );

    let res = time_stamp_token::verify_time_stamp_token(
        &token_der,
        &pes_signature,
        &pes_cert,
        core::slice::from_ref(&pki.root_cert),
    );
    assert_eq!(res, Err(time_stamp_token::TimeStampTokenError::SigningCertificateMismatch));
}

#[test]
fn test_verify_time_stamp_token_fails_missing_time_stamping_eku() {
    use const_oid::db::rfc5280::ID_KP_TIME_STAMPING;
    use oak_time::make_instant;
    use x509_cert::{
        Version,
        ext::{
            Extension,
            pkix::{BasicConstraints, ExtendedKeyUsage},
        },
    };

    use crate::time_stamp_token::chain_tests::{CertSpec, build_cert, make_ext, p256_key};

    let (pes_signature, pes_cert) = create_test_pes_sig_and_cert();
    let pki = build_test_tsa_pki();
    let base_bc_ext = make_ext(true, &BasicConstraints { ca: false, path_len_constraint: None });
    let make_signer_with_exts = |extensions: Vec<Extension>| {
        build_cert(&CertSpec {
            version: Version::V3,
            serial: 3,
            issuer_cn: "Test TSA Root CA",
            subject_cn: "Test TSA Signer",
            not_before: make_instant!("2026-01-01T00:00:00Z"),
            not_after: make_instant!("2028-01-01T00:00:00Z"),
            subject_key: &pki.signer_key,
            issuer_key: &p256_key(0x11),
            extensions,
        })
    };

    // Baseline with critical id-kp-timeStamping EKU succeeds.
    let valid_signer = make_signer_with_exts(vec![
        base_bc_ext.clone(),
        make_ext(true, &ExtendedKeyUsage(vec![ID_KP_TIME_STAMPING])),
    ]);
    let valid_token_der = build_test_time_stamp_token_der(
        &pes_signature,
        make_instant!("2026-06-15T12:00:00Z"),
        &[&valid_signer],
        "Test TSA Root CA",
        3,
        None,
        &pki.signer_key,
    );
    assert_eq!(
        time_stamp_token::verify_time_stamp_token(
            &valid_token_der,
            &pes_signature,
            &pes_cert,
            core::slice::from_ref(&pki.root_cert),
        ),
        Ok(())
    );

    // Signer cert without ExtendedKeyUsage or with non-critical ExtendedKeyUsage
    // fails per RFC 3161 Section 2.3.
    for bad_exts in [
        vec![base_bc_ext.clone()],
        vec![base_bc_ext, make_ext(false, &ExtendedKeyUsage(vec![ID_KP_TIME_STAMPING]))],
    ] {
        let bad_signer = make_signer_with_exts(bad_exts);
        let token_der = build_test_time_stamp_token_der(
            &pes_signature,
            make_instant!("2026-06-15T12:00:00Z"),
            &[&bad_signer],
            "Test TSA Root CA",
            3,
            None,
            &pki.signer_key,
        );
        let res = time_stamp_token::verify_time_stamp_token(
            &token_der,
            &pes_signature,
            &pes_cert,
            core::slice::from_ref(&pki.root_cert),
        );
        assert_eq!(
            res,
            Err(time_stamp_token::TimeStampTokenError::MissingTimeStampingExtendedKeyUsage)
        );
    }
}

#[test]
fn test_verify_time_stamp_token_fails_non_ca_intermediate() {
    use oak_time::make_instant;
    use x509_cert::{
        Version,
        ext::pkix::{BasicConstraints, KeyUsage, KeyUsages},
    };

    use crate::time_stamp_token::chain_tests::{CertSpec, build_cert, make_ext, p256_key};

    let (pes_signature, pes_cert) = create_test_pes_sig_and_cert();
    let pki = build_test_tsa_pki();

    // Intermediate cert with cA = false!
    let bad_intermediate_cert = build_cert(&CertSpec {
        version: Version::V3,
        serial: 2,
        issuer_cn: "Test TSA Root CA",
        subject_cn: "Test TSA Intermediate CA",
        not_before: make_instant!("2024-01-01T00:00:00Z"),
        not_after: make_instant!("2030-01-01T00:00:00Z"),
        subject_key: &p256_key(0x22),
        issuer_key: &p256_key(0x11),
        extensions: vec![
            make_ext(true, &BasicConstraints { ca: false, path_len_constraint: None }),
            make_ext(true, &KeyUsage(KeyUsages::KeyCertSign.into())),
        ],
    });

    let token_der = build_test_time_stamp_token_der(
        &pes_signature,
        make_instant!("2026-06-15T12:00:00Z"),
        &[&pki.signer_cert, &bad_intermediate_cert],
        "Test TSA Intermediate CA",
        3,
        None,
        &pki.signer_key,
    );

    let res = time_stamp_token::verify_time_stamp_token(
        &token_der,
        &pes_signature,
        &pes_cert,
        core::slice::from_ref(&pki.root_cert),
    );
    assert_eq!(res, Err(time_stamp_token::TimeStampTokenError::MissingCaBasicConstraints));
}

#[test]
fn test_verify_time_stamp_token_fails_signer_is_ca() {
    use const_oid::db::rfc5280::ID_KP_TIME_STAMPING;
    use oak_time::make_instant;
    use x509_cert::{
        Version,
        ext::pkix::{BasicConstraints, ExtendedKeyUsage},
    };

    use crate::time_stamp_token::chain_tests::{CertSpec, build_cert, make_ext, p256_key};

    let (pes_signature, pes_cert) = create_test_pes_sig_and_cert();
    let pki = build_test_tsa_pki();

    // Signer cert with cA = true!
    let ca_signer_cert = build_cert(&CertSpec {
        version: Version::V3,
        serial: 3,
        issuer_cn: "Test TSA Root CA",
        subject_cn: "Test TSA Signer",
        not_before: make_instant!("2026-01-01T00:00:00Z"),
        not_after: make_instant!("2028-01-01T00:00:00Z"),
        subject_key: &pki.signer_key,
        issuer_key: &p256_key(0x11),
        extensions: vec![
            make_ext(true, &BasicConstraints { ca: true, path_len_constraint: None }),
            make_ext(true, &ExtendedKeyUsage(vec![ID_KP_TIME_STAMPING])),
        ],
    });

    let token_der = build_test_time_stamp_token_der(
        &pes_signature,
        make_instant!("2026-06-15T12:00:00Z"),
        &[&ca_signer_cert],
        "Test TSA Root CA",
        3,
        None,
        &pki.signer_key,
    );

    let res = time_stamp_token::verify_time_stamp_token(
        &token_der,
        &pes_signature,
        &pes_cert,
        core::slice::from_ref(&pki.root_cert),
    );
    assert_eq!(res, Err(time_stamp_token::TimeStampTokenError::SignerCertificateIsCa));
}

#[test]
fn test_verify_time_stamp_token_backtracks_across_cross_signed_intermediate() {
    use oak_time::make_instant;
    use x509_cert::Version;

    use crate::time_stamp_token::chain_tests::{
        CertSpec, build_cert, default_ca_extensions, p256_key,
    };

    let (pes_signature, pes_cert) = create_test_pes_sig_and_cert();
    let pki = build_test_tsa_pki();

    // Cross-signed intermediate with the same subject and public key as
    // pki.intermediate_cert, but issued by an untrusted root CA.
    let cross_signed_intermediate = build_cert(&CertSpec {
        version: Version::V3,
        serial: 20,
        issuer_cn: "Untrusted Legacy Root CA",
        subject_cn: "Test TSA Intermediate CA",
        not_before: make_instant!("2024-01-01T00:00:00Z"),
        not_after: make_instant!("2030-01-01T00:00:00Z"),
        subject_key: &p256_key(0x22),
        issuer_key: &p256_key(0x77),
        extensions: default_ca_extensions(None),
    });

    // With only the cross-signed intermediate, chain building fails because its
    // issuer is not in trusted_roots.
    let untrusted_only_token_der = build_test_time_stamp_token_der(
        &pes_signature,
        make_instant!("2026-06-15T12:00:00Z"),
        &[&pki.signer_cert, &cross_signed_intermediate],
        "Test TSA Intermediate CA",
        3,
        None,
        &pki.signer_key,
    );
    assert_eq!(
        time_stamp_token::verify_time_stamp_token(
            &untrusted_only_token_der,
            &pes_signature,
            &pes_cert,
            core::slice::from_ref(&pki.root_cert),
        ),
        Err(time_stamp_token::TimeStampTokenError::UntrustedCertificateChain)
    );

    // Place the dead-end cross-signed intermediate before the valid intermediate;
    // chain discovery backtracks and succeeds via pki.intermediate_cert.
    let token_der = build_test_time_stamp_token_der(
        &pes_signature,
        make_instant!("2026-06-15T12:00:00Z"),
        &[&pki.signer_cert, &cross_signed_intermediate, &pki.intermediate_cert],
        "Test TSA Intermediate CA",
        3,
        None,
        &pki.signer_key,
    );

    let res = time_stamp_token::verify_time_stamp_token(
        &token_der,
        &pes_signature,
        &pes_cert,
        core::slice::from_ref(&pki.root_cert),
    );
    assert_eq!(res, Ok(()));
}
