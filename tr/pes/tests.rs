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

use alloc::{string::ToString, vec, vec::Vec};

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

    let mut pes_confirmation_bytes = Vec::new();
    public_endorsement.encode(&mut pes_confirmation_bytes).expect("failed to encode proto");

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
