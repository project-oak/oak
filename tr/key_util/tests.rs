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

#[cfg(test)]
extern crate std;

use test_util::endorsement_data::EndorsementData;

use crate::{
    convert_pem_to_raw, convert_raw_to_pem, convert_raw_to_verifying_key, equal_keys,
    verify_signature_ecdsa,
};

#[test]
fn test_convert_from_raw() {
    let d = EndorsementData::load_for_rekor_verification();
    let key = convert_raw_to_verifying_key(&d.rekor_public_key);
    assert!(key.is_ok());
}

#[test]
fn test_convert_inverse_left() {
    let d = EndorsementData::load_for_rekor_verification();
    let pem = convert_raw_to_pem(&d.rekor_public_key);
    let actual = convert_pem_to_raw(&pem).expect("could not convert key");
    assert!(equal_keys(&d.rekor_public_key, &actual).expect("could not compare keys"), "{:?}", pem);
}

#[test]
fn test_convert_inverse_right() {
    let d = EndorsementData::load_for_rekor_verification();
    let raw = convert_pem_to_raw(&d.rekor_public_key_pem).expect("could not convert key");
    let actual = convert_raw_to_pem(&raw);
    assert!(
        actual.eq(&d.rekor_public_key_pem),
        "expected: {:?} actual: {:?}",
        &d.rekor_public_key_pem,
        actual
    );
}

#[test]
fn test_verify_signature_ecdsa() {
    let d = EndorsementData::load_for_rekor_verification();
    let result = verify_signature_ecdsa(&d.signature, &d.endorsement, &d.endorser_public_key);
    assert!(result.is_ok());
}

#[test]
fn test_verify_signature_rsa() {
    use rsa::{
        Pkcs1v15Sign, RsaPrivateKey,
        pkcs8::{DecodePrivateKey, EncodePublicKey},
    };
    use sha2::{Digest, Sha256};

    // Static 2048-bit RSA private key (PKCS#8 DER base64).
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

    let priv_key_der =
        base64::Engine::decode(&base64::engine::general_purpose::STANDARD, priv_key_base64)
            .expect("failed to decode base64");
    let priv_key = RsaPrivateKey::from_pkcs8_der(&priv_key_der).expect("failed to parse key");
    let pub_key = priv_key.to_public_key();
    let pub_key_der = pub_key.to_public_key_der().expect("failed to encode").to_vec();

    // 2. Sign some dummy data.
    let data = b"test data";
    let mut hasher = Sha256::new();
    hasher.update(data);
    let hashed = hasher.finalize();
    let signature = priv_key.sign(Pkcs1v15Sign::new::<Sha256>(), &hashed).expect("failed to sign");

    // 3. Verify using our library function.
    let result = crate::verify_signature_rsa(&signature, data, &pub_key_der);
    assert!(result.is_ok());
}
