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

    // Static 2048-bit RSA private key provided by the user.
    let priv_key_base64 = "MIIEvAIBADANBgkqhkiG9w0BAQEFAASCBKYwggSiAgEAAoIBAQC2WuIuMUiD0eBL\
        f0ZZiEqRBTmk+eS9N96u9+ABKb6wNE0t7OJgJ82H5fg0D1zTyBrh40i+x7seAEIH\
        7rWUgDQzNw0ex1DySEjypKnbXnSZMfiiK0zP6X65KqZyAHJqy+G24YIikeCzI2kP\
        iw3Ggh6zfbI2/Tbb/iheB3Q/L8gx0zocYyE2Dbd4QhMu6c2emwViO4/1ViK+2J19\
        kbmv5T66M+Am2RrXilyMEYb8g9oQ9PagS6lfPY/8k6SD0euZ3dCkGDEdPDkpjNOu\
        5Xmk+CSn7neBNp2D+7Q6cPwF/mGFvp4OtljoaxP5avPcmDiPBXVf1Jpmsqnvsvck\
        W3J53DFbAgMBAAECggEACgj1UnJu2aY2kCEIZ4vrApEFi5Ee59THwdwtLRM1ha/T\
        IXhcOstl8ZkTsBW6V4M3C4A89Ba8stlzyMj3oBzwAnOAmtWAHF0i+otaN5K6muWX\
        l6EHYJeqXBk/QJ3KrhrbKHu/dBSQB3um3+6YiviFJP6BTKphlvilEwuY95MzEp7D\
        mky6znVSzc2EP/4dCm6OGM1MQu2NAalbYZSxU6PJvjBQJRtfVnDG3ttZ4bUq4VBe\
        NsAqZ4CUfGDfcCEhD5hI2ILb9wVZRQ8xpZfxgJNilBWiulylJcY9dDwvuoraXw4Q\
        7i9bUPF7X5kDj3mvSOyKHBy1cq8MLPxhCzCEd0FNeQKBgQD4/3t/GH3I29UMH34J\
        6fADIPPX3Q4013t7AdrtBfoQPUk1ox9QrURrmRS/nccSDkyZ2cPxzeyclynSupSV\
        gbnFSW3m4rlcIPmfz8jWGLuF2MOXY39EU6q51r5J5WTt5ldfrhumXW2bpQ0Jfjod\
        6pERFRZvhOMPjbW4p7xHkk9PEwKBgQC7e6S5a4cckEPajaNpqSBgh88ma/uywoiJ\
        qVC7iINXhIsZblvP7ZMc8vjAVq1oQXW/5Q+1mouMS96ZdgHf5Ex5LeVZdoFH+dAp\
        jwBPUz7YagBnzNcTvNXFXfA9l7P4S9xd1ykyE/dOuleEDCbld+ziBwm5fpO9KXug\
        i30Dhm01mQKBgFsMMIA82GHF4JVaPqApZpX+Squ4LSWtVX2ZJBBfixy9DDQMvbqm\
        YMpnY2rdqpkzmVb4hem5PrfTnntrtkEk+mTlgMZYSSci96Q0Ol/vE0LSDFMjErpN\
        TbQ+jb4/nzROccyOwZWHvDiZlbbO7TlbOEhiyZ1lnhFl4/jtfK8/FLj5AoGAVVuv\
        3bO1Ki4Mlp7R/bNAyHJMwAN97x9epr5twVQf6GKyKfvy1TInPpDo7DkKbmMPRzT0\
        +AvK6S9Jw7jUlakNoEZjG1428hwsyB8RVwxhmop4cMn0Sko5Uci5LnG5QJzZUeg6\
        G1C30iJI4hfeRa9aLHZj2Q5mGUOfw7J+UnKLmlECgYBZEhBTeh1vQ56A+ZYetNNX\
        pelwpY3sFIxTn/wB2+iH2vjtybN0unB0+CdJbaSV9dlDLVAzf7Z8hKRszHiifRV1\
        HbDtuPyX00hO3gBdtTL7Cxu2gccPjomjzhV3ZD0J9lKQhtndn+b1BsuJSmjEEVtx\
        uOryJhB6vf4tLUlnixyeaA==";

    let priv_key_der = base64::engine::general_purpose::STANDARD
        .decode(priv_key_base64)
        .expect("failed to decode base64");

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
                    der_bytes: vec![1, 2, 3], // Dummy endorser key
                })),
            }),
        }),
        endorsement_signatures: vec![Signature {
            signature: vec![], // Will fill after signing PAE
            verification_material: Some(VerificationMaterial {
                verification_material: Some(VmOneof::X509Certificate(X509Der {
                    der_bytes: pub_key_der.clone(),
                })),
            }),
        }],
        tlog_receipt: Some(TLogReceipt { entry_id: entry_id.to_string() }),
    };

    // 2. Calculate PAE for signing
    let pae = crate::pae::calculate(endorsement_bytes, &[1, 2, 3], &[0; 64], entry_id);

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

    // 6. Verify!
    let result = verify_pes_confirmation(&pes_confirmation_bytes, &pes_key_set, endorsement_bytes);

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
