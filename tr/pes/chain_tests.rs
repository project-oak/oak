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

use alloc::{format, vec, vec::Vec};

use const_oid::{
    AssociatedOid, ObjectIdentifier,
    db::{
        rfc5280::{
            ANY_EXTENDED_KEY_USAGE, ID_CE_BASIC_CONSTRAINTS, ID_CE_EXT_KEY_USAGE,
            ID_CE_INHIBIT_ANY_POLICY, ID_CE_NAME_CONSTRAINTS, ID_CE_SUBJECT_KEY_IDENTIFIER,
            ID_KP_CODE_SIGNING, ID_KP_SERVER_AUTH, ID_KP_TIME_STAMPING,
        },
        rfc5912::ECDSA_WITH_SHA_256,
    },
};
use oak_time::{Duration, Instant, make_instant};
use p256::{ecdsa::signature::Signer as _, pkcs8::EncodePublicKey as _};
use x509_cert::{
    Certificate, TbsCertificate, Version,
    der::{
        DateTime as DerDateTime, Decode, Encode,
        asn1::{BitString, GeneralizedTime, OctetString},
        flagset::FlagSet,
    },
    ext::{
        Extension,
        pkix::{BasicConstraints, ExtendedKeyUsage, KeyUsage, KeyUsages, SubjectKeyIdentifier},
    },
    serial_number::SerialNumber,
    spki::{AlgorithmIdentifierOwned, SubjectPublicKeyInfoOwned},
    time::{Time, Validity},
};

use super::{
    IssuerAndSerialNumber, MAX_CHAIN_DEPTH, SignerIdentifier, TimeStampTokenError,
    find_signer_certificates, verify_ca_constraints, verify_cert_validity_contains,
    verify_certificate_chain, verify_signer_cert_extensions,
};

struct CertSpec<'a> {
    version: Version,
    serial: u32,
    issuer_cn: &'a str,
    subject_cn: &'a str,
    not_before: Instant,
    not_after: Instant,
    subject_key: &'a p256::ecdsa::SigningKey,
    issuer_key: &'a p256::ecdsa::SigningKey,
    extensions: Vec<Extension>,
}

fn p256_key(seed: u8) -> p256::ecdsa::SigningKey {
    p256::ecdsa::SigningKey::from_slice(&[seed; 32]).expect("valid P-256 secret scalar")
}

fn instant_to_x509_time(instant: Instant) -> Time {
    let secs = u64::try_from(instant.into_unix_seconds()).expect("non-negative timestamp");
    let dt = DerDateTime::from_unix_duration(core::time::Duration::from_secs(secs)).unwrap();
    Time::GeneralTime(GeneralizedTime::from_date_time(dt))
}

fn make_ext<T: AssociatedOid + Encode>(critical: bool, value: &T) -> Extension {
    Extension {
        extn_id: T::OID,
        critical,
        extn_value: OctetString::new(value.to_der().unwrap()).unwrap(),
    }
}

fn raw_ext(extn_id: ObjectIdentifier, critical: bool, raw_der: &[u8]) -> Extension {
    Extension { extn_id, critical, extn_value: OctetString::new(raw_der).unwrap() }
}

fn build_cert(spec: &CertSpec<'_>) -> Certificate {
    let sig_alg = AlgorithmIdentifierOwned { oid: ECDSA_WITH_SHA_256, parameters: None };
    let spki_der = spec.subject_key.verifying_key().to_public_key_der().unwrap();
    let tbs_certificate = TbsCertificate {
        version: spec.version,
        serial_number: SerialNumber::from(spec.serial),
        signature: sig_alg.clone(),
        issuer: format!("CN={}", spec.issuer_cn).parse().unwrap(),
        validity: Validity {
            not_before: instant_to_x509_time(spec.not_before),
            not_after: instant_to_x509_time(spec.not_after),
        },
        subject: format!("CN={}", spec.subject_cn).parse().unwrap(),
        subject_public_key_info: SubjectPublicKeyInfoOwned::from_der(spki_der.as_bytes()).unwrap(),
        issuer_unique_id: None,
        subject_unique_id: None,
        extensions: (!spec.extensions.is_empty()).then(|| spec.extensions.clone()),
    };

    let tbs_der = tbs_certificate.to_der().unwrap();
    let sig: p256::ecdsa::Signature = spec.issuer_key.sign(&tbs_der);
    let sig_der = sig.to_der();

    Certificate {
        tbs_certificate,
        signature_algorithm: sig_alg,
        signature: BitString::from_bytes(sig_der.as_bytes()).unwrap(),
    }
}

fn default_ca_extensions(path_len_constraint: Option<u8>) -> Vec<Extension> {
    vec![
        make_ext(true, &BasicConstraints { ca: true, path_len_constraint }),
        make_ext(true, &KeyUsage(KeyUsages::KeyCertSign.into())),
    ]
}

fn default_signer_extensions() -> Vec<Extension> {
    vec![
        make_ext(true, &BasicConstraints { ca: false, path_len_constraint: None }),
        make_ext(true, &KeyUsage(KeyUsages::DigitalSignature.into())),
        make_ext(true, &ExtendedKeyUsage(vec![ID_KP_TIME_STAMPING])),
    ]
}

#[test]
fn test_find_signer_certificates_by_issuer_serial_and_ski() {
    let root_key = p256_key(0x11);
    let signer_key = p256_key(0x22);
    let other_key = p256_key(0x33);
    let shared_ski = b"shared-tsa-key-id";

    let mut exts_with_ski = default_signer_extensions();
    exts_with_ski.push(make_ext(
        false,
        &SubjectKeyIdentifier(OctetString::new(shared_ski.as_slice()).unwrap()),
    ));

    let older_signer = build_cert(&CertSpec {
        version: Version::V3,
        serial: 10,
        issuer_cn: "Test TSA CA",
        subject_cn: "Test TSA Signer",
        not_before: make_instant!("2024-01-01T00:00:00Z"),
        not_after: make_instant!("2025-01-01T00:00:00Z"),
        subject_key: &signer_key,
        issuer_key: &root_key,
        extensions: exts_with_ski.clone(),
    });
    let renewed_signer = build_cert(&CertSpec {
        version: Version::V3,
        serial: 11,
        issuer_cn: "Test TSA CA",
        subject_cn: "Test TSA Signer",
        not_before: make_instant!("2025-01-01T00:00:00Z"),
        not_after: make_instant!("2028-01-01T00:00:00Z"),
        subject_key: &signer_key,
        issuer_key: &root_key,
        extensions: exts_with_ski,
    });
    let unrelated_cert = build_cert(&CertSpec {
        version: Version::V3,
        serial: 99,
        issuer_cn: "Other CA",
        subject_cn: "Other Cert",
        not_before: make_instant!("2025-01-01T00:00:00Z"),
        not_after: make_instant!("2028-01-01T00:00:00Z"),
        subject_key: &other_key,
        issuer_key: &root_key,
        extensions: default_signer_extensions(),
    });

    let bundle = [older_signer.clone(), unrelated_cert, renewed_signer.clone()];

    // IssuerAndSerialNumber selects only the exact certificate.
    let iasn_sid = SignerIdentifier::IssuerAndSerialNumber(IssuerAndSerialNumber {
        issuer: "CN=Test TSA CA".parse().unwrap(),
        serial_number: SerialNumber::from(11u32),
    });
    assert_eq!(find_signer_certificates(&bundle, &iasn_sid), Ok(vec![&renewed_signer]));

    let missing_iasn = SignerIdentifier::IssuerAndSerialNumber(IssuerAndSerialNumber {
        issuer: "CN=Test TSA CA".parse().unwrap(),
        serial_number: SerialNumber::from(42u32),
    });
    assert_eq!(
        find_signer_certificates(&bundle, &missing_iasn),
        Err(TimeStampTokenError::SignerCertificateNotFound)
    );
    assert_eq!(
        find_signer_certificates(&[], &iasn_sid),
        Err(TimeStampTokenError::SignerCertificateNotFound)
    );

    // SubjectKeyIdentifier returns all matching certificates in wire order so
    // callers can disambiguate renewed certificates sharing a keypair.
    let ski_sid =
        SignerIdentifier::SubjectKeyIdentifier(OctetString::new(shared_ski.as_slice()).unwrap());
    assert_eq!(
        find_signer_certificates(&bundle, &ski_sid),
        Ok(vec![&older_signer, &renewed_signer])
    );

    let unknown_ski = SignerIdentifier::SubjectKeyIdentifier(
        OctetString::new(b"unknown-ski".as_slice()).unwrap(),
    );
    assert_eq!(
        find_signer_certificates(&bundle, &unknown_ski),
        Err(TimeStampTokenError::SignerCertificateNotFound)
    );

    // Malformed SKI DER propagates TimeStampTokenError::Der.
    let malformed_ski_cert = build_cert(&CertSpec {
        version: Version::V3,
        serial: 12,
        issuer_cn: "Test TSA CA",
        subject_cn: "Malformed SKI",
        not_before: make_instant!("2025-01-01T00:00:00Z"),
        not_after: make_instant!("2028-01-01T00:00:00Z"),
        subject_key: &signer_key,
        issuer_key: &root_key,
        extensions: vec![raw_ext(ID_CE_SUBJECT_KEY_IDENTIFIER, false, &[0xFF, 0x00])],
    });
    assert!(matches!(
        find_signer_certificates(&[malformed_ski_cert], &ski_sid),
        Err(TimeStampTokenError::Der(_))
    ));
}

#[test]
fn test_verify_signer_cert_extensions() {
    let root_key = p256_key(0x11);
    let signer_key = p256_key(0x22);
    let make_signer = |version: Version, extensions: Vec<Extension>| {
        build_cert(&CertSpec {
            version,
            serial: 3,
            issuer_cn: "Test TSA CA",
            subject_cn: "Test TSA Signer",
            not_before: make_instant!("2026-01-01T00:00:00Z"),
            not_after: make_instant!("2028-01-01T00:00:00Z"),
            subject_key: &signer_key,
            issuer_key: &root_key,
            extensions,
        })
    };

    // Valid with digitalSignature, with nonRepudiation, or without optional
    // KeyUsage / BasicConstraints, and with non-critical informational
    // extensions.
    assert_eq!(
        verify_signer_cert_extensions(&make_signer(Version::V3, default_signer_extensions())),
        Ok(())
    );

    let non_repudiation_exts = vec![
        make_ext(false, &KeyUsage(KeyUsages::NonRepudiation.into())),
        make_ext(true, &ExtendedKeyUsage(vec![ID_KP_TIME_STAMPING])),
        raw_ext(ID_CE_INHIBIT_ANY_POLICY, false, &[0x02, 0x01, 0x00]),
    ];
    assert_eq!(
        verify_signer_cert_extensions(&make_signer(Version::V3, non_repudiation_exts)),
        Ok(())
    );

    let minimal_exts = vec![make_ext(true, &ExtendedKeyUsage(vec![ID_KP_TIME_STAMPING]))];
    assert_eq!(verify_signer_cert_extensions(&make_signer(Version::V3, minimal_exts)), Ok(()));

    // Non-v3 certificates are rejected.
    for bad_version in [Version::V1, Version::V2] {
        assert_eq!(
            verify_signer_cert_extensions(&make_signer(bad_version, default_signer_extensions())),
            Err(TimeStampTokenError::UnsupportedCertificateVersion)
        );
    }

    // Missing, non-critical, or multi-purpose ExtendedKeyUsage is rejected per
    // RFC 3161 Section 2.3.
    assert_eq!(
        verify_signer_cert_extensions(&make_signer(Version::V3, vec![])),
        Err(TimeStampTokenError::MissingTimeStampingExtendedKeyUsage)
    );
    assert_eq!(
        verify_signer_cert_extensions(&make_signer(
            Version::V3,
            vec![make_ext(false, &ExtendedKeyUsage(vec![ID_KP_TIME_STAMPING]))]
        )),
        Err(TimeStampTokenError::MissingTimeStampingExtendedKeyUsage)
    );
    assert_eq!(
        verify_signer_cert_extensions(&make_signer(
            Version::V3,
            vec![make_ext(true, &ExtendedKeyUsage(vec![ID_KP_TIME_STAMPING, ID_KP_CODE_SIGNING]))]
        )),
        Err(TimeStampTokenError::MissingTimeStampingExtendedKeyUsage)
    );

    // Corrupt ExtendedKeyUsage DER propagates TimeStampTokenError::Der rather
    // than masking as MissingTimeStampingExtendedKeyUsage.
    assert!(matches!(
        verify_signer_cert_extensions(&make_signer(
            Version::V3,
            vec![raw_ext(ID_CE_EXT_KEY_USAGE, true, &[0x30, 0x80])]
        )),
        Err(TimeStampTokenError::Der(_))
    ));

    // Duplicate extension OIDs are rejected per RFC 5280 Section 4.2.
    assert!(matches!(
        verify_signer_cert_extensions(&make_signer(
            Version::V3,
            vec![
                make_ext(true, &ExtendedKeyUsage(vec![ID_KP_TIME_STAMPING])),
                make_ext(false, &SubjectKeyIdentifier(OctetString::new([1, 2]).unwrap())),
                make_ext(false, &SubjectKeyIdentifier(OctetString::new([3, 4]).unwrap())),
            ]
        )),
        Err(TimeStampTokenError::Der(_))
    ));

    // Unrecognized critical extensions on the leaf certificate are rejected.
    let mut unhandled_crit_exts = default_signer_extensions();
    unhandled_crit_exts.push(raw_ext(ID_CE_INHIBIT_ANY_POLICY, true, &[0x02, 0x01, 0x00]));
    assert_eq!(
        verify_signer_cert_extensions(&make_signer(Version::V3, unhandled_crit_exts)),
        Err(TimeStampTokenError::UnhandledCriticalCertificateExtension(ID_CE_INHIBIT_ANY_POLICY))
    );

    // BasicConstraints cA=true on leaf signer is rejected.
    assert_eq!(
        verify_signer_cert_extensions(&make_signer(
            Version::V3,
            vec![
                make_ext(true, &ExtendedKeyUsage(vec![ID_KP_TIME_STAMPING])),
                make_ext(true, &BasicConstraints { ca: true, path_len_constraint: None }),
            ]
        )),
        Err(TimeStampTokenError::SignerCertificateIsCa)
    );

    // KeyUsage without digitalSignature or nonRepudiation is rejected.
    let no_sig_ku = FlagSet::<KeyUsages>::from(KeyUsages::KeyEncipherment);
    assert_eq!(
        verify_signer_cert_extensions(&make_signer(
            Version::V3,
            vec![
                make_ext(true, &ExtendedKeyUsage(vec![ID_KP_TIME_STAMPING])),
                make_ext(true, &KeyUsage(no_sig_ku)),
            ]
        )),
        Err(TimeStampTokenError::MissingSignerDigitalSignatureKeyUsage)
    );
}

#[test]
fn test_verify_ca_constraints() {
    let ca_key = p256_key(0x11);
    let make_ca = |version: Version, extensions: Vec<Extension>| {
        build_cert(&CertSpec {
            version,
            serial: 1,
            issuer_cn: "Test TSA Root CA",
            subject_cn: "Test TSA Root CA",
            not_before: make_instant!("2020-01-01T00:00:00Z"),
            not_after: make_instant!("2035-01-01T00:00:00Z"),
            subject_key: &ca_key,
            issuer_key: &ca_key,
            extensions,
        })
    };

    // Valid CA with pathLenConstraint = 1 allows 0 or 1 intermediates below and
    // rejects 2.
    let ca_pathlen_1 = make_ca(Version::V3, default_ca_extensions(Some(1)));
    assert_eq!(verify_ca_constraints(&ca_pathlen_1, 0), Ok(()));
    assert_eq!(verify_ca_constraints(&ca_pathlen_1, 1), Ok(()));
    assert_eq!(
        verify_ca_constraints(&ca_pathlen_1, 2),
        Err(TimeStampTokenError::PathLenConstraintExceeded)
    );

    // Non-v3 CA certificate is rejected.
    assert_eq!(
        verify_ca_constraints(&make_ca(Version::V1, default_ca_extensions(None)), 0),
        Err(TimeStampTokenError::UnsupportedCertificateVersion)
    );

    // Missing or cA=false BasicConstraints is rejected; corrupt DER (or u8
    // overflow on pathLenConstraint = 256) propagates TimeStampTokenError::Der.
    assert_eq!(
        verify_ca_constraints(&make_ca(Version::V3, vec![]), 0),
        Err(TimeStampTokenError::MissingCaBasicConstraints)
    );
    assert_eq!(
        verify_ca_constraints(
            &make_ca(
                Version::V3,
                vec![make_ext(true, &BasicConstraints { ca: false, path_len_constraint: None })]
            ),
            0
        ),
        Err(TimeStampTokenError::MissingCaBasicConstraints)
    );
    // SEQUENCE { BOOLEAN TRUE, INTEGER 256 } -> 30 07 01 01 ff 02 02 01 00
    assert!(matches!(
        verify_ca_constraints(
            &make_ca(
                Version::V3,
                vec![raw_ext(
                    ID_CE_BASIC_CONSTRAINTS,
                    true,
                    &[0x30, 0x07, 0x01, 0x01, 0xFF, 0x02, 0x02, 0x01, 0x00]
                )]
            ),
            0
        ),
        Err(TimeStampTokenError::Der(_))
    ));

    // KeyUsage without keyCertSign is rejected.
    assert_eq!(
        verify_ca_constraints(
            &make_ca(
                Version::V3,
                vec![
                    make_ext(true, &BasicConstraints { ca: true, path_len_constraint: None }),
                    make_ext(true, &KeyUsage(KeyUsages::DigitalSignature.into())),
                ]
            ),
            0
        ),
        Err(TimeStampTokenError::MissingKeyCertSignKeyUsage)
    );

    // CA ExtendedKeyUsage permits id-kp-timeStamping or anyExtendedKeyUsage
    // (critical or non-critical) and rejects unrelated purposes such as
    // id-kp-serverAuth.
    for (critical, allowed_oid) in
        [(false, ID_KP_TIME_STAMPING), (true, ID_KP_TIME_STAMPING), (false, ANY_EXTENDED_KEY_USAGE)]
    {
        let mut exts = default_ca_extensions(None);
        exts.push(make_ext(critical, &ExtendedKeyUsage(vec![allowed_oid])));
        assert_eq!(verify_ca_constraints(&make_ca(Version::V3, exts), 0), Ok(()));
    }

    for critical in [false, true] {
        let mut tls_only_ca_exts = default_ca_extensions(None);
        tls_only_ca_exts.push(make_ext(critical, &ExtendedKeyUsage(vec![ID_KP_SERVER_AUTH])));
        assert_eq!(
            verify_ca_constraints(&make_ca(Version::V3, tls_only_ca_exts), 0),
            Err(TimeStampTokenError::InvalidCaExtendedKeyUsage)
        );
    }

    // Critical NameConstraints on a CA certificate is rejected as unhandled.
    let mut name_constrained_exts = default_ca_extensions(None);
    name_constrained_exts.push(raw_ext(ID_CE_NAME_CONSTRAINTS, true, &[0x30, 0x00]));
    assert_eq!(
        verify_ca_constraints(&make_ca(Version::V3, name_constrained_exts), 0),
        Err(TimeStampTokenError::UnhandledCriticalCertificateExtension(ID_CE_NAME_CONSTRAINTS))
    );
}

#[test]
fn test_verify_certificate_chain_validity_and_self_issued_path_len() {
    let root_key = p256_key(0x11);
    let rollover_key = p256_key(0x12);
    let sub_ca_key = p256_key(0x22);
    let signer_key = p256_key(0x33);

    let not_before = make_instant!("2026-01-01T00:00:00Z");
    let not_after = make_instant!("2028-01-01T00:00:00Z");

    let root_pathlen_0 = build_cert(&CertSpec {
        version: Version::V3,
        serial: 1,
        issuer_cn: "Test TSA Root CA",
        subject_cn: "Test TSA Root CA",
        not_before,
        not_after,
        subject_key: &root_key,
        issuer_key: &root_key,
        extensions: default_ca_extensions(Some(0)),
    });

    // Self-issued key-rollover intermediate (`subject == issuer`) does not
    // increment non-self-issued intermediate count per RFC 5280 Section 6.1.4(l).
    let self_issued_rollover = build_cert(&CertSpec {
        version: Version::V3,
        serial: 2,
        issuer_cn: "Test TSA Root CA",
        subject_cn: "Test TSA Root CA",
        not_before,
        not_after,
        subject_key: &rollover_key,
        issuer_key: &root_key,
        extensions: default_ca_extensions(None),
    });
    let leaf_under_rollover = build_cert(&CertSpec {
        version: Version::V3,
        serial: 3,
        issuer_cn: "Test TSA Root CA",
        subject_cn: "Test TSA Signer",
        not_before,
        not_after,
        subject_key: &signer_key,
        issuer_key: &rollover_key,
        extensions: default_signer_extensions(),
    });

    // Exact validity boundary checks (`not_before` and `not_after` inclusive).
    assert_eq!(verify_cert_validity_contains(&leaf_under_rollover, not_before), Ok(()));
    assert_eq!(verify_cert_validity_contains(&leaf_under_rollover, not_after), Ok(()));
    assert_eq!(
        verify_cert_validity_contains(&leaf_under_rollover, not_before - Duration::from_nanos(1)),
        Err(TimeStampTokenError::CertificateValidityPeriod)
    );
    assert_eq!(
        verify_cert_validity_contains(&leaf_under_rollover, not_after + Duration::from_nanos(1)),
        Err(TimeStampTokenError::CertificateValidityPeriod)
    );

    // Empty trusted roots fails immediately.
    assert_eq!(
        verify_certificate_chain(&leaf_under_rollover, &[], &[], not_before),
        Err(TimeStampTokenError::EmptyTrustedRoots)
    );

    // Direct leaf-anchor match succeeds.
    assert_eq!(
        verify_certificate_chain(
            &leaf_under_rollover,
            &[],
            core::slice::from_ref(&leaf_under_rollover),
            not_before,
        ),
        Ok(())
    );

    // Self-issued intermediate under pathLenConstraint=0 root succeeds.
    assert_eq!(
        verify_certificate_chain(
            &leaf_under_rollover,
            &[leaf_under_rollover.clone(), self_issued_rollover],
            core::slice::from_ref(&root_pathlen_0),
            not_before,
        ),
        Ok(())
    );

    // Non-self-issued intermediate under pathLenConstraint=0 root fails with
    // PathLenConstraintExceeded.
    let non_self_issued_sub_ca = build_cert(&CertSpec {
        version: Version::V3,
        serial: 4,
        issuer_cn: "Test TSA Root CA",
        subject_cn: "Test TSA Sub CA",
        not_before,
        not_after,
        subject_key: &sub_ca_key,
        issuer_key: &root_key,
        extensions: default_ca_extensions(None),
    });
    let leaf_under_sub_ca = build_cert(&CertSpec {
        version: Version::V3,
        serial: 5,
        issuer_cn: "Test TSA Sub CA",
        subject_cn: "Test TSA Signer",
        not_before,
        not_after,
        subject_key: &signer_key,
        issuer_key: &sub_ca_key,
        extensions: default_signer_extensions(),
    });
    assert_eq!(
        verify_certificate_chain(
            &leaf_under_sub_ca,
            &[leaf_under_sub_ca.clone(), non_self_issued_sub_ca],
            core::slice::from_ref(&root_pathlen_0),
            not_before,
        ),
        Err(TimeStampTokenError::PathLenConstraintExceeded)
    );
}

#[test]
fn test_verify_certificate_chain_max_depth_error_precedence_and_dos_bound() {
    let validation_time = make_instant!("2026-06-15T12:00:00Z");
    let not_before = make_instant!("2025-01-01T00:00:00Z");
    let not_after = make_instant!("2030-01-01T00:00:00Z");

    // 1. Build a chain of N certificates (`[leaf, I_1, ..., I_{N-2}, root]`) and
    //    verify exact MAX_CHAIN_DEPTH acceptance vs MAX_CHAIN_DEPTH + 1 rejection.
    let build_chain_of_len = |chain_len: usize| -> (Certificate, Vec<Certificate>, Certificate) {
        assert!(chain_len >= 2);
        let keys: Vec<p256::ecdsa::SigningKey> =
            (0..chain_len).map(|i| p256_key(u8::try_from(i + 1).unwrap())).collect();
        let names: Vec<alloc::string::String> = (0..chain_len)
            .map(|i| {
                if i == 0 {
                    "Leaf TSA Signer".into()
                } else if i + 1 == chain_len {
                    "Root TSA CA".into()
                } else {
                    format!("Intermediate CA {i}")
                }
            })
            .collect();

        let root = build_cert(&CertSpec {
            version: Version::V3,
            serial: 100,
            issuer_cn: &names[chain_len - 1],
            subject_cn: &names[chain_len - 1],
            not_before,
            not_after,
            subject_key: &keys[chain_len - 1],
            issuer_key: &keys[chain_len - 1],
            extensions: default_ca_extensions(None),
        });

        let mut intermediates = Vec::new();
        for i in 1..(chain_len - 1) {
            intermediates.push(build_cert(&CertSpec {
                version: Version::V3,
                serial: u32::try_from(100 + i).unwrap(),
                issuer_cn: &names[i + 1],
                subject_cn: &names[i],
                not_before,
                not_after,
                subject_key: &keys[i],
                issuer_key: &keys[i + 1],
                extensions: default_ca_extensions(None),
            }));
        }

        let leaf = build_cert(&CertSpec {
            version: Version::V3,
            serial: 200,
            issuer_cn: &names[1],
            subject_cn: &names[0],
            not_before,
            not_after,
            subject_key: &keys[0],
            issuer_key: &keys[1],
            extensions: default_signer_extensions(),
        });

        let mut token_certs = vec![leaf.clone()];
        token_certs.extend(intermediates);
        (leaf, token_certs, root)
    };

    let (leaf_ok, certs_ok, root_ok) = build_chain_of_len(MAX_CHAIN_DEPTH);
    assert_eq!(
        verify_certificate_chain(
            &leaf_ok,
            &certs_ok,
            core::slice::from_ref(&root_ok),
            validation_time
        ),
        Ok(())
    );

    let (leaf_too_deep, certs_too_deep, root_too_deep) = build_chain_of_len(MAX_CHAIN_DEPTH + 1);
    assert_eq!(
        verify_certificate_chain(
            &leaf_too_deep,
            &certs_too_deep,
            core::slice::from_ref(&root_too_deep),
            validation_time
        ),
        Err(TimeStampTokenError::UntrustedCertificateChain)
    );

    // 2. Rolled-over intermediate CAs sharing a Subject DN: an untrusted valid
    //    intermediate must report UntrustedCertificateChain rather than being
    //    clobbered by SignatureVerification or CertificateValidityPeriod from an
    //    expired wrong-key cert with the same Subject DN, regardless of certificate
    //    order in token_certs or tsa_root_certs.
    let unrelated_root_key = p256_key(0x90);
    let untrusted_root_key = p256_key(0x91);
    let new_interm_key = p256_key(0x92);
    let old_interm_key = p256_key(0x93);
    let leaf_key = p256_key(0x94);

    let unrelated_trusted_root = build_cert(&CertSpec {
        version: Version::V3,
        serial: 1,
        issuer_cn: "Trusted Root CA",
        subject_cn: "Trusted Root CA",
        not_before,
        not_after,
        subject_key: &unrelated_root_key,
        issuer_key: &unrelated_root_key,
        extensions: default_ca_extensions(None),
    });
    let interm_new = build_cert(&CertSpec {
        version: Version::V3,
        serial: 2,
        issuer_cn: "Untrusted Root CA",
        subject_cn: "Shared Intermediate CA",
        not_before,
        not_after,
        subject_key: &new_interm_key,
        issuer_key: &untrusted_root_key,
        extensions: default_ca_extensions(None),
    });
    let interm_old_wrong_key = build_cert(&CertSpec {
        version: Version::V3,
        serial: 3,
        issuer_cn: "Untrusted Root CA",
        subject_cn: "Shared Intermediate CA",
        not_before: make_instant!("2020-01-01T00:00:00Z"),
        not_after: make_instant!("2024-01-01T00:00:00Z"),
        subject_key: &old_interm_key,
        issuer_key: &untrusted_root_key,
        extensions: default_ca_extensions(None),
    });
    let leaf = build_cert(&CertSpec {
        version: Version::V3,
        serial: 4,
        issuer_cn: "Shared Intermediate CA",
        subject_cn: "TSA Signer",
        not_before,
        not_after,
        subject_key: &leaf_key,
        issuer_key: &new_interm_key,
        extensions: default_signer_extensions(),
    });

    for roots in [
        vec![unrelated_trusted_root.clone()],
        vec![unrelated_trusted_root.clone(), interm_old_wrong_key.clone()],
    ] {
        for bundle in [
            vec![leaf.clone(), interm_new.clone(), interm_old_wrong_key.clone()],
            vec![leaf.clone(), interm_old_wrong_key.clone(), interm_new.clone()],
        ] {
            assert_eq!(
                verify_certificate_chain(&leaf, &bundle, &roots, validation_time),
                Err(TimeStampTokenError::UntrustedCertificateChain)
            );
        }
    }

    // 3. Adversarial bundle of 20 distinct self-issued CA certificates sharing the
    //    same Subject DN and signing key is bounded by MAX_CHAIN_VERIFICATIONS
    //    rather than exploring P(20, 8) permutations.
    let loop_key = p256_key(0xA5);
    let loop_leaf = build_cert(&CertSpec {
        version: Version::V3,
        serial: 500,
        issuer_cn: "Loop CA",
        subject_cn: "Loop Leaf",
        not_before,
        not_after,
        subject_key: &leaf_key,
        issuer_key: &loop_key,
        extensions: default_signer_extensions(),
    });
    let mut adversarial_bundle: Vec<Certificate> = (1..=20)
        .map(|serial| {
            build_cert(&CertSpec {
                version: Version::V3,
                serial,
                issuer_cn: "Loop CA",
                subject_cn: "Loop CA",
                not_before,
                not_after,
                subject_key: &loop_key,
                issuer_key: &loop_key,
                extensions: default_ca_extensions(None),
            })
        })
        .collect();
    adversarial_bundle.insert(0, loop_leaf.clone());

    assert_eq!(
        verify_certificate_chain(
            &loop_leaf,
            &adversarial_bundle,
            core::slice::from_ref(&unrelated_trusted_root),
            validation_time,
        ),
        Err(TimeStampTokenError::UntrustedCertificateChain)
    );
}
