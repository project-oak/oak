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

use alloc::vec;

use base64::{Engine as _, engine::general_purpose::STANDARD};
use const_oid::{
    ObjectIdentifier,
    db::rfc5912::{
        ECDSA_WITH_SHA_256, ECDSA_WITH_SHA_384, ECDSA_WITH_SHA_512, ID_EC_PUBLIC_KEY, ID_SHA_1,
        ID_SHA_256, ID_SHA_384, ID_SHA_512, RSA_ENCRYPTION, SECP_256_R_1, SECP_384_R_1,
        SHA_1_WITH_RSA_ENCRYPTION, SHA_256_WITH_RSA_ENCRYPTION, SHA_384_WITH_RSA_ENCRYPTION,
        SHA_512_WITH_RSA_ENCRYPTION,
    },
};
use ecdsa::signature::hazmat::PrehashSigner as _;
use oak_digest::{Sha256, Sha384, Sha512};
use rsa::{
    BigUint, Pkcs1v15Sign, RsaPrivateKey, RsaPublicKey,
    pkcs8::{DecodePrivateKey as _, EncodePublicKey as _},
    traits::PublicKeyParts as _,
};
use x509_cert::{
    der::{Any, Decode, Tag, asn1::BitString},
    serial_number::SerialNumber,
    spki::{AlgorithmIdentifierOwned, SubjectPublicKeyInfoOwned},
};

use super::{
    ContentInfo, DigestAlgorithm, MIN_RSA_MODULUS_BITS, SignatureAlgorithm, SignedData,
    TimeStampTokenError, verify_certificate_signature, verify_spki_signature,
};
use crate::tests::TEST_RSA_2048_PKCS8_DER_B64;

fn alg_id(oid: ObjectIdentifier, parameters: Option<Any>) -> AlgorithmIdentifierOwned {
    AlgorithmIdentifierOwned { oid, parameters }
}

fn malformed_non_empty_null() -> Any {
    Any::new(Tag::Null, [0xDE, 0xAD]).expect("should construct raw Any with Tag::Null")
}

fn build_synthetic_rsa_spki(modulus_bits: usize) -> SubjectPublicKeyInfoOwned {
    assert!(modulus_bits >= 2);
    let byte_len = modulus_bits.div_ceil(8);
    let mut modulus_be = vec![0u8; byte_len];
    // Set the exact MSB for `modulus_bits` and LSB = 1 so the modulus has exact
    // bit length `modulus_bits` and is odd.
    let top_bit = (modulus_bits - 1) % 8;
    modulus_be[0] = 1u8 << top_bit;
    *modulus_be.last_mut().unwrap() |= 0x01;
    let n = BigUint::from_bytes_be(&modulus_be);
    let e = BigUint::from(65537u32);
    let pub_key = RsaPublicKey::new(n, e).expect("valid synthetic RSA public key components");
    assert_eq!(pub_key.n().bits(), modulus_bits);
    let spki_doc = pub_key.to_public_key_der().expect("should encode RSA SPKI DER");
    SubjectPublicKeyInfoOwned::from_der(spki_doc.as_bytes()).expect("should parse RSA SPKI DER")
}

fn build_test_rsa_2048_key_and_spki() -> (RsaPrivateKey, SubjectPublicKeyInfoOwned) {
    let pkcs8_der = STANDARD
        .decode(TEST_RSA_2048_PKCS8_DER_B64)
        .expect("should decode static RSA PKCS#8 base64");
    let priv_key =
        RsaPrivateKey::from_pkcs8_der(&pkcs8_der).expect("should parse RSA PKCS#8 private key");
    let spki_doc =
        priv_key.to_public_key().to_public_key_der().expect("should encode RSA SPKI DER");
    let spki =
        SubjectPublicKeyInfoOwned::from_der(spki_doc.as_bytes()).expect("should parse RSA SPKI");
    (priv_key, spki)
}

fn build_test_p256_key_and_spki() -> (p256::ecdsa::SigningKey, SubjectPublicKeyInfoOwned) {
    let signing_key =
        p256::ecdsa::SigningKey::from_slice(&[0x42; 32]).expect("valid P-256 secret scalar");
    let verifying_key = *signing_key.verifying_key();
    let spki_doc = verifying_key.to_public_key_der().expect("should encode P-256 SPKI DER");
    let spki = SubjectPublicKeyInfoOwned::from_der(spki_doc.as_bytes())
        .expect("should parse P-256 SPKI DER");
    (signing_key, spki)
}

#[test]
fn test_digest_algorithm_from_algorithm_and_digest() {
    for (oid, expected) in [
        (ID_SHA_256, DigestAlgorithm::Sha256),
        (ID_SHA_384, DigestAlgorithm::Sha384),
        (ID_SHA_512, DigestAlgorithm::Sha512),
    ] {
        assert_eq!(DigestAlgorithm::from_algorithm(&alg_id(oid, None)), Ok(expected));
        assert_eq!(DigestAlgorithm::from_algorithm(&alg_id(oid, Some(Any::null()))), Ok(expected));
    }

    let msg = b"rfc3161 digest test payload";
    assert_eq!(DigestAlgorithm::Sha256.digest(msg).as_ref(), Sha256::from_contents(msg).as_ref());
    assert_eq!(DigestAlgorithm::Sha384.digest(msg).as_ref(), Sha384::from_contents(msg).as_ref());
    assert_eq!(DigestAlgorithm::Sha512.digest(msg).as_ref(), Sha512::from_contents(msg).as_ref());

    // Unsupported digest OID (e.g. SHA-1).
    assert_eq!(
        DigestAlgorithm::from_algorithm(&alg_id(ID_SHA_1, None)),
        Err(TimeStampTokenError::UnsupportedDigestAlgorithm(ID_SHA_1))
    );

    // Non-NULL parameters and malformed non-empty NULL parameters must be
    // rejected per RFC 5754 Section 2 and ITU-T X.690 Section 8.8.2.
    let oid_param = Any::encode_from(&ID_SHA_256).unwrap();
    assert_eq!(
        DigestAlgorithm::from_algorithm(&alg_id(ID_SHA_256, Some(oid_param))),
        Err(TimeStampTokenError::InvalidDigestAlgorithmParameters(ID_SHA_256))
    );
    assert_eq!(
        DigestAlgorithm::from_algorithm(&alg_id(ID_SHA_512, Some(malformed_non_empty_null()))),
        Err(TimeStampTokenError::InvalidDigestAlgorithmParameters(ID_SHA_512))
    );
}

#[test]
fn test_signature_algorithm_from_x509_algorithm() {
    for (oid, digest_alg) in [
        (SHA_256_WITH_RSA_ENCRYPTION, DigestAlgorithm::Sha256),
        (SHA_384_WITH_RSA_ENCRYPTION, DigestAlgorithm::Sha384),
        (SHA_512_WITH_RSA_ENCRYPTION, DigestAlgorithm::Sha512),
    ] {
        assert_eq!(
            SignatureAlgorithm::from_x509_algorithm(&alg_id(oid, None)),
            Ok(SignatureAlgorithm::RsaPkcs1v15(digest_alg))
        );
        assert_eq!(
            SignatureAlgorithm::from_x509_algorithm(&alg_id(oid, Some(Any::null()))),
            Ok(SignatureAlgorithm::RsaPkcs1v15(digest_alg))
        );
        let non_null = Any::encode_from(&ID_SHA_256).unwrap();
        assert_eq!(
            SignatureAlgorithm::from_x509_algorithm(&alg_id(oid, Some(non_null))),
            Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(oid))
        );
        assert_eq!(
            SignatureAlgorithm::from_x509_algorithm(&alg_id(oid, Some(malformed_non_empty_null()))),
            Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(oid))
        );
    }

    for (oid, digest_alg) in [
        (ECDSA_WITH_SHA_256, DigestAlgorithm::Sha256),
        (ECDSA_WITH_SHA_384, DigestAlgorithm::Sha384),
        (ECDSA_WITH_SHA_512, DigestAlgorithm::Sha512),
    ] {
        assert_eq!(
            SignatureAlgorithm::from_x509_algorithm(&alg_id(oid, None)),
            Ok(SignatureAlgorithm::Ecdsa(digest_alg))
        );
        // RFC 5758 Section 3.2 requires ECDSA signature algorithm parameters to
        // be omitted (even NULL is forbidden).
        assert_eq!(
            SignatureAlgorithm::from_x509_algorithm(&alg_id(oid, Some(Any::null()))),
            Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(oid))
        );
        let non_null = Any::encode_from(&SECP_256_R_1).unwrap();
        assert_eq!(
            SignatureAlgorithm::from_x509_algorithm(&alg_id(oid, Some(non_null))),
            Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(oid))
        );
    }

    // Unsupported combined signature OID (sha1WithRSAEncryption).
    assert_eq!(
        SignatureAlgorithm::from_x509_algorithm(&alg_id(SHA_1_WITH_RSA_ENCRYPTION, None)),
        Err(TimeStampTokenError::UnsupportedSignatureAlgorithm(SHA_1_WITH_RSA_ENCRYPTION))
    );

    // Public-key OIDs (`rsaEncryption`, `id-ecPublicKey`) are only valid in CMS
    // `SignerInfo.signatureAlgorithm` (paired with `digestAlgorithm`), never in
    // X.509 `Certificate.signatureAlgorithm`.
    for params in [None, Some(Any::null())] {
        assert_eq!(
            SignatureAlgorithm::from_x509_algorithm(&alg_id(RSA_ENCRYPTION, params.clone())),
            Err(TimeStampTokenError::UnsupportedSignatureAlgorithm(RSA_ENCRYPTION))
        );
        assert_eq!(
            SignatureAlgorithm::from_x509_algorithm(&alg_id(ID_EC_PUBLIC_KEY, params)),
            Err(TimeStampTokenError::UnsupportedSignatureAlgorithm(ID_EC_PUBLIC_KEY))
        );
    }
}

#[test]
fn test_signature_algorithm_from_cms_algorithms() {
    // Invalid `digest_alg_id` errors must propagate and take precedence over
    // `sig_alg`.
    assert_eq!(
        SignatureAlgorithm::from_cms_algorithms(
            &alg_id(ID_SHA_1, None),
            &alg_id(SHA_1_WITH_RSA_ENCRYPTION, None)
        ),
        Err(TimeStampTokenError::UnsupportedDigestAlgorithm(ID_SHA_1))
    );
    let bad_digest_param = Any::encode_from(&ID_SHA_256).unwrap();
    assert_eq!(
        SignatureAlgorithm::from_cms_algorithms(
            &alg_id(ID_SHA_256, Some(bad_digest_param)),
            &alg_id(RSA_ENCRYPTION, None)
        ),
        Err(TimeStampTokenError::InvalidDigestAlgorithmParameters(ID_SHA_256))
    );
    assert_eq!(
        SignatureAlgorithm::from_cms_algorithms(
            &alg_id(ID_SHA_256, Some(malformed_non_empty_null())),
            &alg_id(RSA_ENCRYPTION, None)
        ),
        Err(TimeStampTokenError::InvalidDigestAlgorithmParameters(ID_SHA_256))
    );

    for (digest_oid, digest_alg) in [
        (ID_SHA_256, DigestAlgorithm::Sha256),
        (ID_SHA_384, DigestAlgorithm::Sha384),
        (ID_SHA_512, DigestAlgorithm::Sha512),
    ] {
        let digest_id = alg_id(digest_oid, None);

        // RSA_ENCRYPTION in SignerInfo.signatureAlgorithm (None or NULL params).
        assert_eq!(
            SignatureAlgorithm::from_cms_algorithms(&digest_id, &alg_id(RSA_ENCRYPTION, None)),
            Ok(SignatureAlgorithm::RsaPkcs1v15(digest_alg))
        );
        assert_eq!(
            SignatureAlgorithm::from_cms_algorithms(
                &digest_id,
                &alg_id(RSA_ENCRYPTION, Some(Any::null()))
            ),
            Ok(SignatureAlgorithm::RsaPkcs1v15(digest_alg))
        );
        let non_null_rsa_param = Any::encode_from(&ID_SHA_256).unwrap();
        assert_eq!(
            SignatureAlgorithm::from_cms_algorithms(
                &digest_id,
                &alg_id(RSA_ENCRYPTION, Some(non_null_rsa_param))
            ),
            Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(RSA_ENCRYPTION))
        );
        assert_eq!(
            SignatureAlgorithm::from_cms_algorithms(
                &digest_id,
                &alg_id(RSA_ENCRYPTION, Some(malformed_non_empty_null()))
            ),
            Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(RSA_ENCRYPTION))
        );

        // Legacy fallback: ID_EC_PUBLIC_KEY in SignerInfo.signatureAlgorithm
        // (None or NULL params).
        assert_eq!(
            SignatureAlgorithm::from_cms_algorithms(&digest_id, &alg_id(ID_EC_PUBLIC_KEY, None)),
            Ok(SignatureAlgorithm::Ecdsa(digest_alg))
        );
        assert_eq!(
            SignatureAlgorithm::from_cms_algorithms(
                &digest_id,
                &alg_id(ID_EC_PUBLIC_KEY, Some(Any::null()))
            ),
            Ok(SignatureAlgorithm::Ecdsa(digest_alg))
        );
        let curve_param = Any::encode_from(&SECP_256_R_1).unwrap();
        assert_eq!(
            SignatureAlgorithm::from_cms_algorithms(
                &digest_id,
                &alg_id(ID_EC_PUBLIC_KEY, Some(curve_param))
            ),
            Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(ID_EC_PUBLIC_KEY))
        );
        assert_eq!(
            SignatureAlgorithm::from_cms_algorithms(
                &digest_id,
                &alg_id(ID_EC_PUBLIC_KEY, Some(malformed_non_empty_null()))
            ),
            Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(ID_EC_PUBLIC_KEY))
        );
    }

    // Combined signature OIDs: matching (both RSA and ECDSA), invalid params,
    // and incompatible digest algorithms.
    for rsa_params in [None, Some(Any::null())] {
        assert_eq!(
            SignatureAlgorithm::from_cms_algorithms(
                &alg_id(ID_SHA_384, None),
                &alg_id(SHA_384_WITH_RSA_ENCRYPTION, rsa_params)
            ),
            Ok(SignatureAlgorithm::RsaPkcs1v15(DigestAlgorithm::Sha384))
        );
    }
    assert_eq!(
        SignatureAlgorithm::from_cms_algorithms(
            &alg_id(ID_SHA_256, None),
            &alg_id(SHA_256_WITH_RSA_ENCRYPTION, Some(malformed_non_empty_null()))
        ),
        Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(SHA_256_WITH_RSA_ENCRYPTION))
    );
    assert_eq!(
        SignatureAlgorithm::from_cms_algorithms(
            &alg_id(ID_SHA_512, None),
            &alg_id(ECDSA_WITH_SHA_512, None)
        ),
        Ok(SignatureAlgorithm::Ecdsa(DigestAlgorithm::Sha512))
    );
    assert_eq!(
        SignatureAlgorithm::from_cms_algorithms(
            &alg_id(ID_SHA_256, None),
            &alg_id(ECDSA_WITH_SHA_384, Some(Any::null()))
        ),
        Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(ECDSA_WITH_SHA_384))
    );
    assert_eq!(
        SignatureAlgorithm::from_cms_algorithms(
            &alg_id(ID_SHA_256, None),
            &alg_id(ECDSA_WITH_SHA_384, None)
        ),
        Err(TimeStampTokenError::IncompatibleDigestAndSignatureAlgorithms {
            digest_alg: ID_SHA_256,
            sig_alg: ECDSA_WITH_SHA_384,
        })
    );
    assert_eq!(
        SignatureAlgorithm::from_cms_algorithms(
            &alg_id(ID_SHA_512, None),
            &alg_id(SHA_256_WITH_RSA_ENCRYPTION, Some(Any::null()))
        ),
        Err(TimeStampTokenError::IncompatibleDigestAndSignatureAlgorithms {
            digest_alg: ID_SHA_512,
            sig_alg: SHA_256_WITH_RSA_ENCRYPTION,
        })
    );

    // Unsupported signature OID.
    assert_eq!(
        SignatureAlgorithm::from_cms_algorithms(
            &alg_id(ID_SHA_256, None),
            &alg_id(SHA_1_WITH_RSA_ENCRYPTION, None)
        ),
        Err(TimeStampTokenError::UnsupportedSignatureAlgorithm(SHA_1_WITH_RSA_ENCRYPTION))
    );
}

#[test]
fn test_verify_spki_signature_ecdsa_hashes_and_errors() {
    let (signing_key, p256_spki) = build_test_p256_key_and_spki();
    let msg = b"message signed with P-256 across SHA-256, SHA-384, and SHA-512";

    // Valid P-256 verification across SHA-256, SHA-384, and SHA-512 (exercising
    // RFC 6979 Section 2.3.2 truncation on wider hashes), plus negative checks
    // for tampered messages, mismatched hash algorithms, and non-DER signatures.
    for (digest_alg, wrong_digest_alg) in [
        (DigestAlgorithm::Sha256, DigestAlgorithm::Sha384),
        (DigestAlgorithm::Sha384, DigestAlgorithm::Sha512),
        (DigestAlgorithm::Sha512, DigestAlgorithm::Sha256),
    ] {
        let prehash = digest_alg.digest(msg);
        let sig: p256::ecdsa::Signature =
            signing_key.sign_prehash(prehash.as_ref()).expect("should sign prehash");
        let sig_der = sig.to_der();
        assert_eq!(
            verify_spki_signature(
                &p256_spki,
                SignatureAlgorithm::Ecdsa(digest_alg),
                msg,
                sig_der.as_bytes()
            ),
            Ok(())
        );
        assert!(matches!(
            verify_spki_signature(
                &p256_spki,
                SignatureAlgorithm::Ecdsa(digest_alg),
                b"tampered message",
                sig_der.as_bytes()
            ),
            Err(TimeStampTokenError::SignatureVerification(_))
        ));
        assert!(matches!(
            verify_spki_signature(
                &p256_spki,
                SignatureAlgorithm::Ecdsa(wrong_digest_alg),
                msg,
                sig_der.as_bytes()
            ),
            Err(TimeStampTokenError::SignatureVerification(_))
        ));
        // Raw fixed-width IEEE P1363 `r || s` bytes must be rejected where ASN.1
        // DER `ECDSA-Sig-Value` is required.
        assert!(matches!(
            verify_spki_signature(
                &p256_spki,
                SignatureAlgorithm::Ecdsa(digest_alg),
                msg,
                sig.to_bytes().as_slice()
            ),
            Err(TimeStampTokenError::SignatureVerification(_))
        ));
    }

    // Malformed DER signature bytes.
    assert!(matches!(
        verify_spki_signature(
            &p256_spki,
            SignatureAlgorithm::Ecdsa(DigestAlgorithm::Sha256),
            msg,
            b"not valid der"
        ),
        Err(TimeStampTokenError::SignatureVerification(_))
    ));

    // SPKI OID mismatch: RSA signature algorithm with EC SPKI.
    assert!(matches!(
        verify_spki_signature(
            &p256_spki,
            SignatureAlgorithm::RsaPkcs1v15(DigestAlgorithm::Sha256),
            msg,
            b"unused"
        ),
        Err(TimeStampTokenError::SignatureVerification(err)) if err.contains("rsaEncryption")
    ));

    // Missing EC curve parameters in SPKI.
    let mut missing_curve_spki = p256_spki.clone();
    missing_curve_spki.algorithm.parameters = None;
    assert!(matches!(
        verify_spki_signature(
            &missing_curve_spki,
            SignatureAlgorithm::Ecdsa(DigestAlgorithm::Sha256),
            msg,
            b"unused"
        ),
        Err(TimeStampTokenError::SignatureVerification(err)) if err.contains("missing EC curve")
    ));

    // Non-OID EC parameters in SPKI (e.g. NULL `implicitCurve`, forbidden in
    // PKIX by RFC 5480 Section 2.1.1).
    let mut null_curve_spki = p256_spki.clone();
    null_curve_spki.algorithm.parameters = Some(Any::null());
    assert!(matches!(
        verify_spki_signature(
            &null_curve_spki,
            SignatureAlgorithm::Ecdsa(DigestAlgorithm::Sha256),
            msg,
            b"unused"
        ),
        Err(TimeStampTokenError::SignatureVerification(_))
    ));

    // Unsupported EC curve (secp384r1).
    let mut p384_curve_spki = p256_spki.clone();
    p384_curve_spki.algorithm.parameters = Some(Any::encode_from(&SECP_384_R_1).unwrap());
    assert!(matches!(
        verify_spki_signature(
            &p384_curve_spki,
            SignatureAlgorithm::Ecdsa(DigestAlgorithm::Sha256),
            msg,
            b"unused"
        ),
        Err(TimeStampTokenError::SignatureVerification(err)) if err.contains("unsupported EC curve")
    ));

    // Malformed SEC1 public key point bytes on a SECP_256_R_1 SPKI.
    let mut invalid_point_spki = p256_spki;
    invalid_point_spki.subject_public_key =
        BitString::new(0, [0x04, 0x01, 0x02]).expect("valid BitString");
    assert!(matches!(
        verify_spki_signature(
            &invalid_point_spki,
            SignatureAlgorithm::Ecdsa(DigestAlgorithm::Sha256),
            msg,
            b"unused"
        ),
        Err(TimeStampTokenError::SignatureVerification(_))
    ));
}

#[test]
fn test_verify_spki_signature_rsa_hashes_and_errors() {
    let (rsa_priv_key, rsa_spki) = build_test_rsa_2048_key_and_spki();
    let msg = b"message signed with RSA-2048 across SHA-256, SHA-384, and SHA-512";

    for (digest_alg, wrong_digest_alg) in [
        (DigestAlgorithm::Sha256, DigestAlgorithm::Sha384),
        (DigestAlgorithm::Sha384, DigestAlgorithm::Sha512),
        (DigestAlgorithm::Sha512, DigestAlgorithm::Sha256),
    ] {
        let prehash = digest_alg.digest(msg);
        let sig = match digest_alg {
            DigestAlgorithm::Sha256 => rsa_priv_key
                .sign(Pkcs1v15Sign::new::<sha2::Sha256>(), prehash.as_ref())
                .expect("should sign RSA-SHA256"),
            DigestAlgorithm::Sha384 => rsa_priv_key
                .sign(Pkcs1v15Sign::new::<sha2::Sha384>(), prehash.as_ref())
                .expect("should sign RSA-SHA384"),
            DigestAlgorithm::Sha512 => rsa_priv_key
                .sign(Pkcs1v15Sign::new::<sha2::Sha512>(), prehash.as_ref())
                .expect("should sign RSA-SHA512"),
        };
        assert_eq!(
            verify_spki_signature(
                &rsa_spki,
                SignatureAlgorithm::RsaPkcs1v15(digest_alg),
                msg,
                &sig
            ),
            Ok(())
        );
        assert!(matches!(
            verify_spki_signature(
                &rsa_spki,
                SignatureAlgorithm::RsaPkcs1v15(digest_alg),
                b"tampered message",
                &sig
            ),
            Err(TimeStampTokenError::SignatureVerification(_))
        ));
        assert!(matches!(
            verify_spki_signature(
                &rsa_spki,
                SignatureAlgorithm::RsaPkcs1v15(wrong_digest_alg),
                msg,
                &sig
            ),
            Err(TimeStampTokenError::SignatureVerification(_))
        ));
    }

    // Malformed / wrong-length RSA signature bytes.
    assert!(matches!(
        verify_spki_signature(
            &rsa_spki,
            SignatureAlgorithm::RsaPkcs1v15(DigestAlgorithm::Sha256),
            msg,
            b"short sig"
        ),
        Err(TimeStampTokenError::SignatureVerification(_))
    ));

    // RSA modulus smaller than MIN_RSA_MODULUS_BITS (2048), including the exact
    // off-by-one boundary `MIN_RSA_MODULUS_BITS - 1` (2047 bits, which still
    // occupies 256 bytes in big-endian representation).
    for small_bits in [1024, MIN_RSA_MODULUS_BITS - 1] {
        let small_rsa_spki = build_synthetic_rsa_spki(small_bits);
        let expected_err_substr = alloc::format!(
            "RSA modulus too small: {small_bits} bits, minimum is {MIN_RSA_MODULUS_BITS}"
        );
        assert!(matches!(
            verify_spki_signature(
                &small_rsa_spki,
                SignatureAlgorithm::RsaPkcs1v15(DigestAlgorithm::Sha256),
                b"message",
                &[0u8; 256]
            ),
            Err(TimeStampTokenError::SignatureVerification(err)) if err.contains(&expected_err_substr)
        ));
    }

    // SPKI OID mismatch: ECDSA signature algorithm with RSA SPKI.
    assert!(matches!(
        verify_spki_signature(
            &rsa_spki,
            SignatureAlgorithm::Ecdsa(DigestAlgorithm::Sha256),
            b"message",
            b"unused"
        ),
        Err(TimeStampTokenError::SignatureVerification(err)) if err.contains("id-ecPublicKey")
    ));

    // RFC 3279 Section 2.3.1 requires NULL parameters in rsaEncryption SPKI.
    let mut missing_null_rsa_spki = rsa_spki.clone();
    missing_null_rsa_spki.algorithm.parameters = None;
    assert!(matches!(
        verify_spki_signature(
            &missing_null_rsa_spki,
            SignatureAlgorithm::RsaPkcs1v15(DigestAlgorithm::Sha256),
            msg,
            &[0u8; 256]
        ),
        Err(TimeStampTokenError::SignatureVerification(_))
    ));

    let mut malformed_null_rsa_spki = rsa_spki;
    malformed_null_rsa_spki.algorithm.parameters = Some(malformed_non_empty_null());
    assert!(matches!(
        verify_spki_signature(
            &malformed_null_rsa_spki,
            SignatureAlgorithm::RsaPkcs1v15(DigestAlgorithm::Sha256),
            msg,
            &[0u8; 256]
        ),
        Err(TimeStampTokenError::SignatureVerification(_))
    ));
}

#[test]
fn test_verify_certificate_signature_valid_and_errors() {
    let token_b64 = include_str!("testdata/globalsign_token.b64").trim();
    let token_der = STANDARD.decode(token_b64).expect("valid base64 in globalsign_token.b64");
    let content_info = ContentInfo::from_der(&token_der).expect("should parse ContentInfo");
    let signed_data =
        content_info.content.decode_as::<SignedData<'_>>().expect("should parse SignedData");
    let certs = signed_data.certificates.expect("expected certificates in fixture");
    let subject = &certs[0];
    let issuer = &certs[1];

    // Valid RSA-SHA384 certificate signature from GlobalSign fixture.
    assert_eq!(verify_certificate_signature(subject, issuer), Ok(()));

    // Mismatched tbsCertificate.signature vs Certificate.signatureAlgorithm
    // (different OID).
    let mut mismatched_oid_cert = subject.clone();
    mismatched_oid_cert.tbs_certificate.signature =
        alg_id(SHA_256_WITH_RSA_ENCRYPTION, Some(Any::null()));
    assert!(matches!(
        verify_certificate_signature(&mismatched_oid_cert, issuer),
        Err(TimeStampTokenError::SignatureVerification(err))
            if err.contains("does not match signatureAlgorithm")
    ));

    // Same OID (`sha384WithRSAEncryption`), mismatched parameters (`None` vs
    // `Some(NULL)`): both are valid X.509 RSA algorithm identifiers, but RFC
    // 5280 Section 4.1.1.2 requires exact equality between inner and outer
    // fields.
    let mut mismatched_params_cert = subject.clone();
    mismatched_params_cert.signature_algorithm = alg_id(SHA_384_WITH_RSA_ENCRYPTION, None);
    assert!(matches!(
        verify_certificate_signature(&mismatched_params_cert, issuer),
        Err(TimeStampTokenError::SignatureVerification(err))
            if err.contains("does not match signatureAlgorithm")
    ));

    // Invalid signatureAlgorithm parameters on matching fields.
    let mut invalid_params_cert = subject.clone();
    let bad_ecdsa_alg = alg_id(ECDSA_WITH_SHA_256, Some(Any::null()));
    invalid_params_cert.tbs_certificate.signature = bad_ecdsa_alg.clone();
    invalid_params_cert.signature_algorithm = bad_ecdsa_alg;
    assert_eq!(
        verify_certificate_signature(&invalid_params_cert, issuer),
        Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(ECDSA_WITH_SHA_256))
    );

    // Non-zero unused bits in Certificate.signature BIT STRING (with canonical
    // zeroed trailing bit per ITU-T X.690 Section 11.2.1).
    let mut nonzero_unused_bits_cert = subject.clone();
    let mut sig_bytes = subject.signature.raw_bytes().to_vec();
    *sig_bytes.last_mut().unwrap() &= !0x01;
    nonzero_unused_bits_cert.signature =
        BitString::new(1, sig_bytes).expect("valid BitString with 1 unused zero bit");
    assert!(matches!(
        verify_certificate_signature(&nonzero_unused_bits_cert, issuer),
        Err(TimeStampTokenError::SignatureVerification(err)) if err.contains("unused bits")
    ));

    // End-to-end cryptographic verification failures reaching
    // `verify_spki_signature`:
    // 1. Corrupted byte in `subject.signature` (with 0 unused bits).
    let mut corrupted_sig_cert = subject.clone();
    let mut corrupted_sig_bytes = subject.signature.raw_bytes().to_vec();
    corrupted_sig_bytes[0] ^= 0xFF;
    corrupted_sig_cert.signature =
        BitString::new(0, corrupted_sig_bytes).expect("valid BitString with 0 unused bits");
    assert!(matches!(
        verify_certificate_signature(&corrupted_sig_cert, issuer),
        Err(TimeStampTokenError::SignatureVerification(_))
    ));

    // 2. Tampered `tbsCertificate` field without re-signing.
    let mut tampered_tbs_cert = subject.clone();
    tampered_tbs_cert.tbs_certificate.serial_number = SerialNumber::from(1u32);
    assert!(matches!(
        verify_certificate_signature(&tampered_tbs_cert, issuer),
        Err(TimeStampTokenError::SignatureVerification(_))
    ));

    // 3. Wrong issuer public key (`subject` did not self-sign itself).
    assert!(matches!(
        verify_certificate_signature(subject, subject),
        Err(TimeStampTokenError::SignatureVerification(_))
    ));
}
