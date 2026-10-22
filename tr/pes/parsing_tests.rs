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

use alloc::{vec, vec::Vec};

use base64::{Engine as _, engine::general_purpose::STANDARD};
use const_oid::{
    ObjectIdentifier,
    db::{
        rfc4519::{C, CN, O, OU},
        rfc5911::{ID_CONTENT_TYPE, ID_MESSAGE_DIGEST, ID_SIGNED_DATA},
        rfc5912::{ID_SHA_256, ID_SHA_384, SHA_384_WITH_RSA_ENCRYPTION},
    },
};
use oak_time::{Instant, make_instant};
use rsa::BigUint;
use x509_cert::{
    attr::AttributeTypeAndValue,
    der::{
        Any, Decode, Encode, Header, Length, Tag,
        asn1::{IntRef, OctetString, PrintableStringRef, SetOfVec},
    },
    ext::{
        Extension, Extensions,
        pkix::{certpolicy::PolicyInformation, name::GeneralName},
    },
    name::{Name, RdnSequence, RelativeDistinguishedName},
    serial_number::SerialNumber,
    spki::AlgorithmIdentifierOwned,
};

use crate::time_stamp_token;

fn make_printable_name(rdns: &[(ObjectIdentifier, &str)]) -> Name {
    RdnSequence(
        rdns.iter()
            .map(|&(oid, val)| {
                RelativeDistinguishedName(
                    SetOfVec::try_from(vec![AttributeTypeAndValue {
                        oid,
                        value: Any::encode_from(&PrintableStringRef::new(val).unwrap()).unwrap(),
                    }])
                    .unwrap(),
                )
            })
            .collect::<Vec<_>>(),
    )
}

fn dec_serial(dec: &str) -> SerialNumber {
    let bytes = BigUint::parse_bytes(dec.as_bytes(), 10).unwrap().to_bytes_be();
    SerialNumber::new(&bytes).unwrap()
}

fn hex_octet_string(hex_str: &str) -> OctetString {
    OctetString::new(hex::decode(hex_str).unwrap()).unwrap()
}

#[test]
fn test_parse_globalsign_time_stamp_token_fields() {
    let token_b64 = include_str!("testdata/globalsign_token.b64").trim();
    let token_der = STANDARD.decode(token_b64).expect("valid base64 in globalsign_token.b64");

    let content_info =
        time_stamp_token::ContentInfo::from_der(&token_der).expect("should parse ContentInfo");
    assert_eq!(content_info.to_der().expect("should encode ContentInfo"), token_der);
    assert_eq!(content_info.content_type, ID_SIGNED_DATA);

    let signed_data = content_info
        .content
        .decode_as::<time_stamp_token::SignedData<'_>>()
        .expect("should parse SignedData");
    assert_eq!(signed_data.version, 3);
    assert_eq!(
        signed_data.digest_algorithms.as_slice(),
        &[AlgorithmIdentifierOwned { oid: ID_SHA_384, parameters: None }]
    );
    assert_eq!(signed_data.encap_content_info.econtent_type, time_stamp_token::ID_CT_TST_INFO);
    assert!(signed_data.crls.is_none());

    let tst_info_der =
        signed_data.encap_content_info.econtent.expect("missing econtent").as_bytes();
    let tst_info = time_stamp_token::TstInfo::from_der(tst_info_der).expect("should parse TSTInfo");

    let expected_tsa_name = make_printable_name(&[
        (C, "BE"),
        (O, "GlobalSign nv-sa"),
        (CN, "Globalsign R45 TSA for CodeSign 202510"),
    ]);
    let expected_issuer = make_printable_name(&[
        (C, "BE"),
        (O, "GlobalSign nv-sa"),
        (CN, "GlobalSign Offline R45 Timestamping CA 2025"),
    ]);

    assert_eq!(
        tst_info,
        time_stamp_token::TstInfo {
            version: 1,
            policy: ObjectIdentifier::new_unwrap("1.3.6.1.4.1.4146.2.3.2.2"),
            message_imprint: time_stamp_token::MessageImprint {
                hash_algorithm: AlgorithmIdentifierOwned {
                    oid: ID_SHA_256,
                    parameters: Some(Any::null()),
                },
                hashed_message: hex_octet_string(
                    "a652069ea3304f8da0101144810be7e8a8f1bb52d29ad903d2d04723989b217d"
                ),
            },
            serial_number: dec_serial("560364811862049158511804299324352445174953666932"),
            gen_time: time_stamp_token::Rfc3161GeneralizedTime(make_instant!(
                "2026-08-17T13:16:12Z"
            )),
            accuracy: Some(time_stamp_token::Accuracy {
                seconds: Some(1),
                millis: None,
                micros: None,
            }),
            ordering: false,
            nonce: None,
            tsa: Some(GeneralName::DirectoryName(expected_tsa_name.clone())),
            extensions: None,
        }
    );

    let certs = signed_data.certificates.as_ref().expect("expected certificates").as_slice();
    assert_eq!(certs.len(), 4);
    assert_eq!(certs[0].tbs_certificate.subject, expected_tsa_name);
    assert_eq!(certs[1].tbs_certificate.subject, expected_issuer);
    assert_eq!(
        certs[2].tbs_certificate.subject,
        make_printable_name(&[
            (C, "BE"),
            (O, "GlobalSign nv-sa"),
            (CN, "GlobalSign Timestamping Root R45"),
        ])
    );
    assert_eq!(
        certs[3].tbs_certificate.subject,
        make_printable_name(&[
            (OU, "GlobalSign Root CA - R6"),
            (O, "GlobalSign"),
            (CN, "GlobalSign"),
        ])
    );
    assert_eq!(
        signed_data.to_der().expect("should encode SignedData"),
        content_info.content.to_der().unwrap()
    );

    assert_eq!(signed_data.signer_infos.len(), 1);
    let signer_info = signed_data.signer_infos.get(0).unwrap();
    assert_eq!(signer_info.version, 1);

    let expected_signer_serial = dec_serial("176051310414682256565311512954554756068");
    assert_eq!(
        signer_info.sid,
        time_stamp_token::SignerIdentifier::IssuerAndSerialNumber(
            time_stamp_token::IssuerAndSerialNumber {
                issuer: expected_issuer.clone(),
                serial_number: expected_signer_serial.clone(),
            }
        )
    );
    assert_eq!(
        signer_info.digest_algorithm,
        AlgorithmIdentifierOwned { oid: ID_SHA_384, parameters: None }
    );
    assert_eq!(
        signer_info.signature_algorithm,
        AlgorithmIdentifierOwned {
            oid: SHA_384_WITH_RSA_ENCRYPTION,
            parameters: Some(Any::null())
        }
    );
    assert!(signer_info.unsigned_attrs.is_none());

    let signed_attrs = signer_info.signed_attrs.as_ref().expect("expected signed_attrs");
    assert_eq!(signed_attrs.len(), 4);

    assert_eq!(signed_attrs.get(0).unwrap().oid, ID_CONTENT_TYPE);
    assert_eq!(
        signed_attrs
            .get(0)
            .unwrap()
            .values
            .get(0)
            .unwrap()
            .decode_as::<ObjectIdentifier>()
            .unwrap(),
        time_stamp_token::ID_CT_TST_INFO
    );

    assert_eq!(signed_attrs.get(1).unwrap().oid, time_stamp_token::ID_AA_CMS_ALGORITHM_PROTECTION);
    let cap = signed_attrs
        .get(1)
        .unwrap()
        .values
        .get(0)
        .unwrap()
        .decode_as::<time_stamp_token::CmsAlgorithmProtection>()
        .unwrap();
    assert_eq!(
        cap,
        time_stamp_token::CmsAlgorithmProtection {
            digest_algorithm: AlgorithmIdentifierOwned { oid: ID_SHA_384, parameters: None },
            signature_algorithm: Some(AlgorithmIdentifierOwned {
                oid: SHA_384_WITH_RSA_ENCRYPTION,
                parameters: Some(Any::null()),
            }),
            mac_algorithm: None,
        }
    );

    assert_eq!(signed_attrs.get(2).unwrap().oid, ID_MESSAGE_DIGEST);
    assert_eq!(
        signed_attrs.get(2).unwrap().values.get(0).unwrap().decode_as::<OctetString>().unwrap(),
        hex_octet_string(
            "9a396a54b6faec688cabfcc385712eb7b69d5815a805764e5ed92f244ddf2cb1c1b181786226b108f1bcd95f9c405108"
        )
    );

    assert_eq!(signed_attrs.get(3).unwrap().oid, time_stamp_token::ID_AA_SIGNING_CERTIFICATE_V2);
    let sc_v2 = signed_attrs
        .get(3)
        .unwrap()
        .values
        .get(0)
        .unwrap()
        .decode_as::<time_stamp_token::SigningCertificateV2>()
        .unwrap();
    assert_eq!(
        sc_v2,
        time_stamp_token::SigningCertificateV2 {
            certs: vec![time_stamp_token::EssCertIdV2 {
                hash_algorithm: AlgorithmIdentifierOwned { oid: ID_SHA_256, parameters: None },
                cert_hash: hex_octet_string(
                    "832ad72e523fdeac83fa4694bce7c6cc261764882866566588c8adca3a838551"
                ),
                issuer_serial: Some(time_stamp_token::IssuerSerial {
                    issuer: vec![GeneralName::DirectoryName(expected_issuer)],
                    serial_number: expected_signer_serial,
                }),
            }],
            policies: None,
        }
    );

    // Verify `SignedData` accepts and round-trips `certificates` even when not
    // in canonical DER `SET OF` (`DerOrd`) byte order (e.g. chain order).
    let mut non_der_sorted_signed_data = signed_data.clone();
    non_der_sorted_signed_data.certificates.as_mut().unwrap().reverse();
    let reencoded = non_der_sorted_signed_data
        .to_der()
        .expect("should encode SignedData with reversed certificates");
    let redecoded = time_stamp_token::SignedData::from_der(&reencoded)
        .expect("should decode SignedData with non-DER-sorted certificates");
    assert_eq!(redecoded, non_der_sorted_signed_data);
}

#[test]
fn test_ess_cert_id_v2_default_hash_algorithm_der() {
    let cert_hash =
        hex_octet_string("832ad72e523fdeac83fa4694bce7c6cc261764882866566588c8adca3a838551");

    // Encoding with the default hashAlgorithm (`id-sha256` with `None`
    // parameters) omits the field per RFC 5035 Section 4 and ITU-T X.690
    // Section 11.5 (so the encoded SEQUENCE contains only `cert_hash`), and
    // decodes back to the same `EssCertIdV2` with `id-sha256`.
    let with_default_sha256 = time_stamp_token::EssCertIdV2 {
        hash_algorithm: AlgorithmIdentifierOwned { oid: ID_SHA_256, parameters: None },
        cert_hash: cert_hash.clone(),
        issuer_serial: None,
    };
    let hash_der = cert_hash.to_der().unwrap();
    let encoded_default = with_default_sha256.to_der().expect("should encode with default sha256");
    assert_eq!(encoded_default, wrap_der(Tag::Sequence, &hash_der));
    assert_eq!(
        time_stamp_token::EssCertIdV2::from_der(&encoded_default).expect("should decode"),
        with_default_sha256
    );

    // Explicitly encoding the default `id-sha256` AlgorithmIdentifier in DER
    // must be rejected during decoding per ITU-T X.690 Section 11.5.
    let alg_der = AlgorithmIdentifierOwned { oid: ID_SHA_256, parameters: None }.to_der().unwrap();
    let mut inner = Vec::with_capacity(alg_der.len() + hash_der.len());
    inner.extend_from_slice(&alg_der);
    inner.extend_from_slice(&hash_der);
    let mut explicit_default_der =
        Header::new(Tag::Sequence, Length::try_from(inner.len()).unwrap())
            .unwrap()
            .to_der()
            .unwrap();
    explicit_default_der.extend_from_slice(&inner);
    assert!(time_stamp_token::EssCertIdV2::from_der(&explicit_default_der).is_err());

    // Explicit `NULL` parameters (`{ algorithm id-sha256, parameters NULL }`)
    // and non-default OIDs (`id-sha384`) have distinct wire encodings from
    // `{ algorithm id-sha256 }` and round-trip identically.
    for non_default_alg in [
        AlgorithmIdentifierOwned { oid: ID_SHA_256, parameters: Some(Any::null()) },
        AlgorithmIdentifierOwned { oid: ID_SHA_384, parameters: None },
    ] {
        let ess = time_stamp_token::EssCertIdV2 {
            hash_algorithm: non_default_alg,
            cert_hash: cert_hash.clone(),
            issuer_serial: None,
        };
        let encoded = ess.to_der().expect("should encode non-default hash_algorithm");
        assert_eq!(time_stamp_token::EssCertIdV2::from_der(&encoded).expect("should decode"), ess);
    }
}

fn wrap_der(tag: Tag, value: &[u8]) -> Vec<u8> {
    let mut der =
        Header::new(tag, Length::try_from(value.len()).unwrap()).unwrap().to_der().unwrap();
    der.extend_from_slice(value);
    der
}

#[test]
fn test_rfc3161_generalized_time_der() {
    // 1. Fractional-second round-tripping (".5Z" and ".123456789Z").
    let half_sec_der = wrap_der(Tag::GeneralizedTime, b"20260817131612.5Z");
    let half_sec = time_stamp_token::Rfc3161GeneralizedTime::from_der(&half_sec_der)
        .expect("should parse .5Z GeneralizedTime");
    assert_eq!(half_sec.0, make_instant!("2026-08-17T13:16:12.500Z"));
    assert_eq!(half_sec.to_der().expect("should encode .5Z"), half_sec_der);

    let nano_sec_der = wrap_der(Tag::GeneralizedTime, b"20260817131612.123456789Z");
    let nano_sec = time_stamp_token::Rfc3161GeneralizedTime::from_der(&nano_sec_der)
        .expect("should parse .123456789Z GeneralizedTime");
    let base_nanos = make_instant!("2026-08-17T13:16:12Z").into_unix_nanos();
    assert_eq!(nano_sec.0, Instant::from_unix_nanos(base_nanos + 123_456_789));
    assert_eq!(nano_sec.to_der().expect("should encode .123456789Z"), nano_sec_der);

    // 2. Rejection of malformed encodings.
    for malformed in [
        &b"20260817131612.50Z"[..],         // trailing zero in fractional seconds
        &b"20260817131612.0Z"[..],          // redundant ".0Z"
        &b"20260817131612.Z"[..],           // bare dot with empty fraction
        &b"20260817131612+0000"[..],        // non-UTC offset instead of 'Z'
        &b"20260817131612"[..],             // missing trailing 'Z'
        &b"20260817235960Z"[..],            // leap second "60Z" (disallowed by X.680 46.3)
        &b"20260817235960.5Z"[..],          // leap second with fractional seconds
        &b"20260817131612.0000000001Z"[..], // >9 fractional digits (sub-nanosecond)
    ] {
        let der = wrap_der(Tag::GeneralizedTime, malformed);
        assert!(
            time_stamp_token::Rfc3161GeneralizedTime::from_der(&der).is_err(),
            "expected error for malformed GeneralizedTime {:?}",
            core::str::from_utf8(malformed)
        );
    }

    // 3. Out-of-range Instant values fail cleanly with der::Error rather than
    //    panicking.
    for out_of_range in [
        Instant::from_unix_nanos(i128::MAX),
        Instant::from_unix_nanos(i128::MIN),
        Instant::from_unix_seconds(-62_167_219_201), // before 0000-01-01T00:00:00Z (year -1)
        Instant::from_unix_seconds(253_402_300_800), // 10000-01-01T00:00:00Z (year 10000)
    ] {
        assert!(time_stamp_token::Rfc3161GeneralizedTime(out_of_range).to_der().is_err());
    }
}

fn sample_tst_info<'a>() -> time_stamp_token::TstInfo<'a> {
    time_stamp_token::TstInfo {
        version: 1,
        policy: ObjectIdentifier::new_unwrap("1.3.6.1.4.1.4146.2.3.2.2"),
        message_imprint: time_stamp_token::MessageImprint {
            hash_algorithm: AlgorithmIdentifierOwned {
                oid: ID_SHA_256,
                parameters: Some(Any::null()),
            },
            hashed_message: hex_octet_string(
                "a652069ea3304f8da0101144810be7e8a8f1bb52d29ad903d2d04723989b217d",
            ),
        },
        serial_number: SerialNumber::from(1u32),
        gen_time: time_stamp_token::Rfc3161GeneralizedTime(make_instant!("2026-08-17T13:16:12Z")),
        accuracy: None,
        ordering: false,
        nonce: None,
        tsa: None,
        extensions: None,
    }
}

#[test]
fn test_tst_info_ordering_der() {
    // 1. `ordering: true` round-tripping.
    let mut tst_true = sample_tst_info();
    tst_true.ordering = true;
    let der_true = tst_true.to_der().expect("should encode TstInfo with ordering: true");
    let decoded_true = time_stamp_token::TstInfo::from_der(&der_true)
        .expect("should decode TstInfo with ordering: true");
    assert_eq!(decoded_true, tst_true);

    // 2. X.690 Section 11.5 rejection of an explicit `BOOLEAN FALSE` (0x01 0x01
    //    0x00)
    // in DER (where `ordering: true` encoded 0x01 0x01 0xff at the end of the
    // SEQUENCE).
    let mut der_explicit_false = der_true;
    assert_eq!(
        &der_explicit_false[der_explicit_false.len() - 3..],
        &[0x01, 0x01, 0xff],
        "expected trailing BOOLEAN TRUE in encoded TstInfo"
    );
    *der_explicit_false.last_mut().unwrap() = 0x00;
    assert!(
        time_stamp_token::TstInfo::from_der(&der_explicit_false).is_err(),
        "explicit BOOLEAN FALSE for DEFAULT FALSE ordering must be rejected in DER"
    );
}

#[test]
fn test_signer_identifier_subject_key_identifier_der() {
    let ski_bytes = hex_octet_string("0102030405060708090a0b0c0d0e0f1011121314");
    let sid = time_stamp_token::SignerIdentifier::SubjectKeyIdentifier(ski_bytes.clone());
    let sid_der = sid.to_der().expect("should encode SubjectKeyIdentifier");
    // `[0] IMPLICIT SubjectKeyIdentifier` must use context-specific primitive tag 0
    // (0x80).
    assert_eq!(sid_der[0], 0x80);
    let decoded_sid = time_stamp_token::SignerIdentifier::from_der(&sid_der)
        .expect("should decode SubjectKeyIdentifier");
    assert_eq!(decoded_sid, sid);

    // Unexpected tag (e.g. OCTET STRING 0x04 instead of SEQUENCE or [0] IMPLICIT)
    // must fail.
    let wrong_tag_der = ski_bytes.to_der().unwrap();
    assert!(time_stamp_token::SignerIdentifier::from_der(&wrong_tag_der).is_err());

    // Round-trip inside `SignerInfo` (version 3 per RFC 5652 Section 5.3 when using
    // SKI).
    let signer_info = time_stamp_token::SignerInfo {
        version: 3,
        sid,
        digest_algorithm: AlgorithmIdentifierOwned { oid: ID_SHA_256, parameters: None },
        signed_attrs: None,
        signature_algorithm: AlgorithmIdentifierOwned {
            oid: SHA_384_WITH_RSA_ENCRYPTION,
            parameters: Some(Any::null()),
        },
        signature: hex_octet_string("deadbeef"),
        unsigned_attrs: None,
    };
    let si_der = signer_info.to_der().expect("should encode SignerInfo with SKI");
    assert_eq!(
        time_stamp_token::SignerInfo::from_der(&si_der).expect("should decode SignerInfo with SKI"),
        signer_info
    );
}

#[test]
fn test_optional_fields_der() {
    // 1. `Accuracy` with `millis` ([0] IMPLICIT) and `micros` ([1] IMPLICIT),
    // `TstInfo.nonce`, and `TstInfo.extensions`.
    let accuracy =
        time_stamp_token::Accuracy { seconds: Some(2), millis: Some(500), micros: Some(750) };
    let accuracy_der = accuracy.to_der().expect("should encode Accuracy");
    assert_eq!(
        time_stamp_token::Accuracy::from_der(&accuracy_der).expect("should decode Accuracy"),
        accuracy
    );

    let nonce_bytes = [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef];
    let ext = Extension {
        extn_id: ObjectIdentifier::new_unwrap("1.2.3.4.5.6"),
        critical: false,
        extn_value: hex_octet_string("0402abcd"),
    };
    let mut tst = sample_tst_info();
    tst.accuracy = Some(accuracy);
    tst.nonce = Some(IntRef::new(&nonce_bytes).unwrap());
    tst.extensions = Some(Extensions::from(vec![ext]));

    let tst_der = tst.to_der().expect("should encode TstInfo with optional fields");
    let decoded_tst = time_stamp_token::TstInfo::from_der(&tst_der)
        .expect("should decode TstInfo with optional fields");
    assert_eq!(decoded_tst, tst);

    // 2. `SigningCertificateV2.policies` round-tripping and tag enforcement.
    let policy_info = PolicyInformation {
        policy_identifier: ObjectIdentifier::new_unwrap("1.3.6.1.4.1.4146.2.3.2.2"),
        policy_qualifiers: None,
    };
    let sc_v2 = time_stamp_token::SigningCertificateV2 {
        certs: vec![time_stamp_token::EssCertIdV2 {
            hash_algorithm: AlgorithmIdentifierOwned { oid: ID_SHA_256, parameters: None },
            cert_hash: hex_octet_string(
                "832ad72e523fdeac83fa4694bce7c6cc261764882866566588c8adca3a838551",
            ),
            issuer_serial: None,
        }],
        policies: Some(vec![policy_info]),
    };
    let sc_v2_der = sc_v2.to_der().expect("should encode SigningCertificateV2 with policies");
    assert_eq!(
        time_stamp_token::SigningCertificateV2::from_der(&sc_v2_der)
            .expect("should decode SigningCertificateV2 with policies"),
        sc_v2
    );

    // Trailing non-SEQUENCE element (e.g. OCTET STRING) in SigningCertificateV2
    // must be rejected.
    let certs_der = sc_v2.certs.to_der().unwrap();
    let trailing_octet_string = hex_octet_string("deadbeef").to_der().unwrap();
    let mut bad_inner = Vec::new();
    bad_inner.extend_from_slice(&certs_der);
    bad_inner.extend_from_slice(&trailing_octet_string);
    let bad_sc_v2_der = wrap_der(Tag::Sequence, &bad_inner);
    assert!(time_stamp_token::SigningCertificateV2::from_der(&bad_sc_v2_der).is_err());
}
