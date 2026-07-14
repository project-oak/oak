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
    oak::attestation::v1::{KeyType, VerifyingKey, VerifyingKeySet},
};
use rsa::{Pkcs1v15Sign, RsaPrivateKey, pkcs8::EncodePublicKey};

use super::*;

#[test]
fn test_verify_pes_confirmation_success() {
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

    let priv_key_base64 = "MIIEvAIBADANBgkqhkiG9w0BAQEFAASCBKYwggSiAgEAAoIBAQCuLvnJf0gAqeKPn6NQrLBJWKd+\
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

    let cert_der = base64::engine::general_purpose::STANDARD
        .decode(cert_base64)
        .expect("failed to decode certificate base64");

    let priv_key_der = base64::engine::general_purpose::STANDARD
        .decode(priv_key_base64)
        .expect("failed to decode private key base64");

    let priv_key = RsaPrivateKey::from_pkcs8_der(&priv_key_der).expect("failed to parse key");
    let pub_key = priv_key.to_public_key();
    let pub_key_der = pub_key.to_public_key_der().expect("failed to encode public key").to_vec();

    let endorsement_bytes = b"{\"artifact\":\"test\"}";
    let entry_id = "test-log-entry";

    // 1. Construct the PublicEndorsement
    let mut public_endorsement = PublicEndorsement {
        name: "endorsements/test".to_string(),
        statement: Some(Statement {
            format: StatementFormat::JsonIntoto.into(),
            serialized: endorsement_bytes.to_vec(),
        }),
        statement_signature: Some(Signature {
            signature: vec![0; 64], // Dummy endorser signature
            verification_material: Some(VerificationMaterial {
                verification_material: Some(VmOneof::EcdsaP256Sha256(EcdsaP256PublicKey {
                    der_bytes: dummy_endorser_key_bytes.clone(),
                })),
            }),
        }),
        endorsement_signatures: vec![Signature {
            signature: vec![], // Will fill after signing PAE
            verification_material: Some(VerificationMaterial {
                verification_material: Some(VmOneof::X509Certificate(X509Der {
                    der_bytes: cert_der,
                })),
            }),
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

    // 6. Verify!
    let result = verify_pes_confirmation(
        &pes_confirmation_bytes,
        &pes_key_set,
        endorsement_bytes,
        &trusted_endorser_key,
    );

    assert!(result.is_ok(), "Verification failed: {:?}", result.err());
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
