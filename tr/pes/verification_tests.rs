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

use alloc::{vec, vec::Vec};

use base64::{Engine as _, engine::general_purpose::STANDARD};
use x509_cert::{
    attr::Attribute,
    der::Any,
    ext::{Extension, Extensions},
};

use super::*;

fn load_globalsign_token_der() -> Vec<u8> {
    let token_b64 = include_str!("testdata/globalsign_token.b64").trim();
    STANDARD.decode(token_b64).expect("valid base64 in globalsign_token.b64")
}

fn make_attr(oid: ObjectIdentifier, values: Vec<Any>) -> Attribute {
    Attribute { oid, values: SetOfVec::try_from(values).unwrap() }
}

fn encode_signed_data(sd: &SignedData<'_>) -> Vec<u8> {
    let sd_der = sd.to_der().unwrap();
    ContentInfo {
        content_type: ID_SIGNED_DATA,
        content: AnyRef::try_from(sd_der.as_slice()).unwrap(),
    }
    .to_der()
    .unwrap()
}

fn verify_signed_attrs_with_cert(
    attrs: &Attributes,
    signer_digest_alg: DigestAlgorithm,
    signer_digest_alg_id: &AlgorithmIdentifierOwned,
    signer_sig_alg_id: &AlgorithmIdentifierOwned,
    tst_info_der: &[u8],
    signer_cert: &Certificate,
) -> Result<(), TimeStampTokenError> {
    let (ess_cert_id, cert_digest_alg) = verify_signed_attrs(
        attrs,
        signer_digest_alg,
        signer_digest_alg_id,
        signer_sig_alg_id,
        tst_info_der,
    )?;
    verify_ess_cert_id(&ess_cert_id, cert_digest_alg, signer_cert)
}

#[test]
fn test_verify_signed_attrs_valid_and_errors() {
    let token_der = load_globalsign_token_der();
    let content_info = ContentInfo::from_der(&token_der).unwrap();
    let signed_data = content_info.content.decode_as::<SignedData<'_>>().unwrap();
    let tst_info_der = signed_data.encap_content_info.econtent.unwrap().as_bytes();
    let certs = signed_data.certificates.as_ref().unwrap();
    let signer_cert = &certs[0];
    let signer_info = signed_data.signer_infos.get(0).unwrap();
    let valid_attrs = signer_info.signed_attrs.as_ref().unwrap();
    let digest_alg_id = &signer_info.digest_algorithm;
    let sig_alg_id = &signer_info.signature_algorithm;

    // 1. Valid GlobalSign signedAttrs (with EssCertIdV2.issuer_serial and
    //    CMSAlgorithmProtection present).
    assert_eq!(
        verify_signed_attrs_with_cert(
            valid_attrs,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            tst_info_der,
            signer_cert,
        ),
        Ok(())
    );

    let signer_cert_der = signer_cert.to_der().unwrap();
    let signer_cert_hash =
        OctetString::new(Sha256::from_contents(&signer_cert_der).as_ref()).unwrap();
    let tst_digest_octets = OctetString::new(Sha384::from_contents(tst_info_der).as_ref()).unwrap();

    let build_attrs = |sc_v2: SigningCertificateV2| -> Attributes {
        let sc_v2_der = sc_v2.to_der().unwrap();
        let mut attrs = Attributes::new();
        attrs
            .insert(make_attr(ID_CONTENT_TYPE, vec![Any::encode_from(&ID_CT_TST_INFO).unwrap()]))
            .unwrap();
        attrs
            .insert(make_attr(
                ID_MESSAGE_DIGEST,
                vec![Any::encode_from(&tst_digest_octets).unwrap()],
            ))
            .unwrap();
        attrs
            .insert(make_attr(
                ID_AA_SIGNING_CERTIFICATE_V2,
                vec![Any::from_der(&sc_v2_der).unwrap()],
            ))
            .unwrap();
        attrs
    };

    // 2. Valid when EssCertIdV2.issuer_serial is omitted (`None`) or accompanied by
    //    a single-valued legacy `id-aa-signingCertificate` attribute.
    let valid_sc_v2_no_is = SigningCertificateV2 {
        certs: vec![EssCertIdV2 {
            hash_algorithm: default_ess_hash_algorithm(),
            cert_hash: signer_cert_hash.clone(),
            issuer_serial: None,
        }],
        policies: None,
    };
    let attrs_ok = build_attrs(valid_sc_v2_no_is.clone());
    assert_eq!(
        verify_signed_attrs_with_cert(
            &attrs_ok,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            tst_info_der,
            signer_cert,
        ),
        Ok(())
    );
    // When `hash_algorithm` is the default, `SigningCertificateV2` omits
    // `hashAlgorithm` on the wire, producing the exact RFC 2634 Section 5.4
    // `SigningCertificate` (`SEQUENCE { certs SEQUENCE OF ESSCertID }`) DER
    // layout.
    let make_legacy_sc_any = |sha1_hash: [u8; 20]| -> Any {
        let der = SigningCertificateV2 {
            certs: vec![EssCertIdV2 {
                hash_algorithm: default_ess_hash_algorithm(),
                cert_hash: OctetString::new(sha1_hash).unwrap(),
                issuer_serial: None,
            }],
            policies: None,
        }
        .to_der()
        .unwrap();
        Any::from_der(&der).unwrap()
    };
    let mut attrs_with_v1 = attrs_ok.clone();
    attrs_with_v1
        .insert(make_attr(ID_AA_SIGNING_CERTIFICATE, vec![make_legacy_sc_any([0u8; 20])]))
        .unwrap();
    assert_eq!(
        verify_signed_attrs_with_cert(
            &attrs_with_v1,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            tst_info_der,
            signer_cert,
        ),
        Ok(())
    );

    // 3. EssCertIdV2.issuer_serial validation (wrong serial, wrong issuer DN, or
    //    empty GeneralNames).
    for bad_issuer_serial in [
        IssuerSerial {
            issuer: vec![GeneralName::DirectoryName(signer_cert.tbs_certificate.issuer.clone())],
            serial_number: SerialNumber::from(1u32),
        },
        IssuerSerial {
            issuer: vec![GeneralName::DirectoryName(signer_cert.tbs_certificate.subject.clone())],
            serial_number: signer_cert.tbs_certificate.serial_number.clone(),
        },
        IssuerSerial {
            issuer: vec![],
            serial_number: signer_cert.tbs_certificate.serial_number.clone(),
        },
    ] {
        let attrs = build_attrs(SigningCertificateV2 {
            certs: vec![EssCertIdV2 {
                hash_algorithm: default_ess_hash_algorithm(),
                cert_hash: signer_cert_hash.clone(),
                issuer_serial: Some(bad_issuer_serial),
            }],
            policies: None,
        });
        assert_eq!(
            verify_signed_attrs_with_cert(
                &attrs,
                DigestAlgorithm::Sha384,
                digest_alg_id,
                sig_alg_id,
                tst_info_der,
                signer_cert,
            ),
            Err(TimeStampTokenError::SigningCertificateMismatch)
        );
    }

    // 4. Missing, wrong OID, or multi-valued content-type attribute.
    let valid_sc_v2_attr = make_attr(
        ID_AA_SIGNING_CERTIFICATE_V2,
        vec![Any::from_der(&valid_sc_v2_no_is.to_der().unwrap()).unwrap()],
    );
    let mut no_ct_attrs = Attributes::new();
    no_ct_attrs
        .insert(make_attr(ID_MESSAGE_DIGEST, vec![Any::encode_from(&tst_digest_octets).unwrap()]))
        .unwrap();
    no_ct_attrs.insert(valid_sc_v2_attr.clone()).unwrap();
    assert_eq!(
        verify_signed_attrs_with_cert(
            &no_ct_attrs,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            tst_info_der,
            signer_cert,
        ),
        Err(TimeStampTokenError::InvalidSignedContentType)
    );

    for bad_ct_values in [
        vec![Any::encode_from(&ID_SIGNED_DATA).unwrap()],
        vec![
            Any::encode_from(&ID_CT_TST_INFO).unwrap(),
            Any::encode_from(&ID_SIGNED_DATA).unwrap(),
        ],
    ] {
        let mut bad_ct_attrs = no_ct_attrs.clone();
        bad_ct_attrs.insert(make_attr(ID_CONTENT_TYPE, bad_ct_values)).unwrap();
        assert_eq!(
            verify_signed_attrs_with_cert(
                &bad_ct_attrs,
                DigestAlgorithm::Sha384,
                digest_alg_id,
                sig_alg_id,
                tst_info_der,
                signer_cert,
            ),
            Err(TimeStampTokenError::InvalidSignedContentType)
        );
    }

    // 5. Missing, non-OctetString, multi-valued, or mismatched message-digest
    //    attribute.
    let mut no_md_attrs = Attributes::new();
    no_md_attrs
        .insert(make_attr(ID_CONTENT_TYPE, vec![Any::encode_from(&ID_CT_TST_INFO).unwrap()]))
        .unwrap();
    no_md_attrs.insert(valid_sc_v2_attr).unwrap();
    assert_eq!(
        verify_signed_attrs_with_cert(
            &no_md_attrs,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            tst_info_der,
            signer_cert,
        ),
        Err(TimeStampTokenError::InvalidMessageDigestAttr)
    );

    for bad_md_values in [
        vec![Any::encode_from(&ID_SHA_256).unwrap()],
        vec![Any::encode_from(&tst_digest_octets).unwrap(), Any::encode_from(&ID_SHA_256).unwrap()],
    ] {
        let mut bad_md_attrs = no_md_attrs.clone();
        bad_md_attrs.insert(make_attr(ID_MESSAGE_DIGEST, bad_md_values)).unwrap();
        assert_eq!(
            verify_signed_attrs_with_cert(
                &bad_md_attrs,
                DigestAlgorithm::Sha384,
                digest_alg_id,
                sig_alg_id,
                tst_info_der,
                signer_cert,
            ),
            Err(TimeStampTokenError::InvalidMessageDigestAttr)
        );
    }

    assert_eq!(
        verify_signed_attrs_with_cert(
            &attrs_ok,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            b"tampered tst_info_der",
            signer_cert,
        ),
        Err(TimeStampTokenError::MessageDigestMismatch)
    );

    // 6. Missing, malformed, multi-valued, empty EssCertIdV2 sequence, or duplicate
    //    SigningCertificateV2 / SigningCertificate attribute.
    let mut no_sc_attrs = Attributes::new();
    no_sc_attrs
        .insert(make_attr(ID_CONTENT_TYPE, vec![Any::encode_from(&ID_CT_TST_INFO).unwrap()]))
        .unwrap();
    no_sc_attrs
        .insert(make_attr(ID_MESSAGE_DIGEST, vec![Any::encode_from(&tst_digest_octets).unwrap()]))
        .unwrap();
    assert_eq!(
        verify_signed_attrs_with_cert(
            &no_sc_attrs,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            tst_info_der,
            signer_cert,
        ),
        Err(TimeStampTokenError::InvalidSigningCertificateAttr)
    );

    for bad_sc_v2_values in [
        vec![Any::null()],
        vec![Any::from_der(&valid_sc_v2_no_is.to_der().unwrap()).unwrap(), Any::null()],
    ] {
        let mut bad_sc_attrs = no_sc_attrs.clone();
        bad_sc_attrs.insert(make_attr(ID_AA_SIGNING_CERTIFICATE_V2, bad_sc_v2_values)).unwrap();
        assert_eq!(
            verify_signed_attrs_with_cert(
                &bad_sc_attrs,
                DigestAlgorithm::Sha384,
                digest_alg_id,
                sig_alg_id,
                tst_info_der,
                signer_cert,
            ),
            Err(TimeStampTokenError::InvalidSigningCertificateAttr)
        );
    }

    let empty_certs_attrs = build_attrs(SigningCertificateV2 { certs: vec![], policies: None });
    assert_eq!(
        verify_signed_attrs_with_cert(
            &empty_certs_attrs,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            tst_info_der,
            signer_cert,
        ),
        Err(TimeStampTokenError::InvalidSigningCertificateAttr)
    );

    // `Attributes` (`SetOfVec<Attribute>`) orders and deduplicates elements by
    // their full DER encoding (`DerOrd`), not by OID alone, so inserting an
    // `Attribute` with the same OID and distinct `values` retains both entries.
    let other_sc_v2 = SigningCertificateV2 {
        certs: vec![EssCertIdV2 {
            hash_algorithm: default_ess_hash_algorithm(),
            cert_hash: OctetString::new([0u8; 32]).unwrap(),
            issuer_serial: None,
        }],
        policies: None,
    };
    let mut dup_v2_attrs = attrs_ok.clone();
    dup_v2_attrs
        .insert(make_attr(
            ID_AA_SIGNING_CERTIFICATE_V2,
            vec![Any::from_der(&other_sc_v2.to_der().unwrap()).unwrap()],
        ))
        .unwrap();
    assert_eq!(dup_v2_attrs.iter().filter(|a| a.oid == ID_AA_SIGNING_CERTIFICATE_V2).count(), 2);
    assert_eq!(
        verify_signed_attrs_with_cert(
            &dup_v2_attrs,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            tst_info_der,
            signer_cert,
        ),
        Err(TimeStampTokenError::InvalidSigningCertificateAttr)
    );

    let mut dup_v1_attrs = attrs_with_v1;
    dup_v1_attrs
        .insert(make_attr(ID_AA_SIGNING_CERTIFICATE, vec![make_legacy_sc_any([1u8; 20])]))
        .unwrap();
    assert_eq!(dup_v1_attrs.iter().filter(|a| a.oid == ID_AA_SIGNING_CERTIFICATE).count(), 2);
    assert_eq!(
        verify_signed_attrs_with_cert(
            &dup_v1_attrs,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            tst_info_der,
            signer_cert,
        ),
        Err(TimeStampTokenError::InvalidSigningCertificateAttr)
    );

    // 7. CMSAlgorithmProtection validation (mismatched digestAlgorithm, mismatched
    //    or missing signatureAlgorithm, present macAlgorithm, or non-CAP value).
    for bad_cap in [
        CmsAlgorithmProtection {
            digest_algorithm: AlgorithmIdentifierOwned { oid: ID_SHA_256, parameters: None },
            signature_algorithm: Some(sig_alg_id.clone()),
            mac_algorithm: None,
        },
        CmsAlgorithmProtection {
            digest_algorithm: digest_alg_id.clone(),
            signature_algorithm: Some(AlgorithmIdentifierOwned {
                oid: SHA_256_WITH_RSA_ENCRYPTION,
                parameters: Some(Any::null()),
            }),
            mac_algorithm: None,
        },
        CmsAlgorithmProtection {
            digest_algorithm: digest_alg_id.clone(),
            signature_algorithm: None,
            mac_algorithm: None,
        },
        CmsAlgorithmProtection {
            digest_algorithm: digest_alg_id.clone(),
            signature_algorithm: Some(sig_alg_id.clone()),
            mac_algorithm: Some(digest_alg_id.clone()),
        },
    ] {
        let cap_der = bad_cap.to_der().unwrap();
        let mut attrs_bad_cap = attrs_ok.clone();
        attrs_bad_cap
            .insert(make_attr(
                ID_AA_CMS_ALGORITHM_PROTECTION,
                vec![Any::from_der(&cap_der).unwrap()],
            ))
            .unwrap();
        assert_eq!(
            verify_signed_attrs_with_cert(
                &attrs_bad_cap,
                DigestAlgorithm::Sha384,
                digest_alg_id,
                sig_alg_id,
                tst_info_der,
                signer_cert,
            ),
            Err(TimeStampTokenError::InvalidCmsAlgorithmProtection)
        );
    }

    let mut attrs_non_cap = attrs_ok.clone();
    attrs_non_cap.insert(make_attr(ID_AA_CMS_ALGORITHM_PROTECTION, vec![Any::null()])).unwrap();
    assert_eq!(
        verify_signed_attrs_with_cert(
            &attrs_non_cap,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            tst_info_der,
            signer_cert,
        ),
        Err(TimeStampTokenError::InvalidCmsAlgorithmProtection)
    );

    // 8. Duplicate unrecognized attribute OID or empty Attribute.values set must be
    //    rejected per RFC 5652 Section 5.3. (`Attributes` is `SetOfVec<Attribute>`,
    //    which deduplicates by full DER encoding rather than by OID, so distinct
    //    attribute values produce two entries with the same OID.)
    let custom_oid = ObjectIdentifier::new_unwrap("1.2.3.4.5.6.7");
    let mut dup_custom_attrs = attrs_ok.clone();
    dup_custom_attrs.insert(make_attr(custom_oid, vec![Any::null()])).unwrap();
    dup_custom_attrs
        .insert(make_attr(custom_oid, vec![Any::encode_from(&ID_SHA_256).unwrap()]))
        .unwrap();
    assert_eq!(dup_custom_attrs.iter().filter(|a| a.oid == custom_oid).count(), 2);
    assert!(matches!(
        verify_signed_attrs_with_cert(
            &dup_custom_attrs,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            tst_info_der,
            signer_cert,
        ),
        Err(TimeStampTokenError::Der(_))
    ));

    let mut empty_val_attrs = attrs_ok;
    empty_val_attrs.insert(make_attr(custom_oid, vec![])).unwrap();
    assert!(matches!(
        verify_signed_attrs_with_cert(
            &empty_val_attrs,
            DigestAlgorithm::Sha384,
            digest_alg_id,
            sig_alg_id,
            tst_info_der,
            signer_cert,
        ),
        Err(TimeStampTokenError::Der(_))
    ));
}

#[test]
fn test_verify_time_stamp_token_structural_and_candidate_precedence_errors() {
    let token_der = load_globalsign_token_der();
    let content_info = ContentInfo::from_der(&token_der).unwrap();
    let signed_data = content_info.content.decode_as::<SignedData<'_>>().unwrap();
    let tst_info_der = signed_data.encap_content_info.econtent.unwrap().as_bytes();
    let tst_info = TstInfo::from_der(tst_info_der).unwrap();
    let certs = signed_data.certificates.as_ref().unwrap();
    let pes_cert = &certs[0];
    let roots = core::slice::from_ref(
        certs.get(3).expect("test data should contain at least 4 certificates"),
    );
    let dummy_sig = &[0u8; 48];

    // Empty trusted roots.
    assert_eq!(
        verify_time_stamp_token(&token_der, dummy_sig, pes_cert, &[]),
        Err(TimeStampTokenError::EmptyTrustedRoots)
    );

    // Unexpected outer ContentInfo contentType.
    let wrong_ci_der = ContentInfo { content_type: ID_CT_TST_INFO, content: content_info.content }
        .to_der()
        .unwrap();
    assert_eq!(
        verify_time_stamp_token(&wrong_ci_der, dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::UnexpectedContentType(ID_CT_TST_INFO))
    );

    // Unsupported SignedData version (RFC 5652 Section 5.1 requires 3 for
    // id-ct-TSTInfo, or 5 when crls contains [1] IMPLICIT
    // OtherRevocationInfoFormat).
    let mut bad_sd_ver = signed_data.clone();
    bad_sd_ver.version = 1;
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&bad_sd_ver), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::UnsupportedSignedDataVersion(1))
    );
    bad_sd_ver.version = 5;
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&bad_sd_ver), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::UnsupportedSignedDataVersion(5))
    );
    let other_rev_seq = AlgorithmIdentifierOwned { oid: ID_SHA_256, parameters: Some(Any::null()) };
    let other_rev_der = ContextSpecificRef {
        tag_number: TagNumber::N1,
        tag_mode: TagMode::Implicit,
        value: &other_rev_seq,
    }
    .to_der()
    .unwrap();
    let mut other_crl_sd = signed_data.clone();
    other_crl_sd.crls = Some(
        SetOfVec::try_from(vec![AnyRef::try_from(other_rev_der.as_slice()).unwrap()]).unwrap(),
    );
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&other_crl_sd), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::UnsupportedSignedDataVersion(3))
    );
    other_crl_sd.version = 5;
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&other_crl_sd), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::MessageImprintMismatch)
    );

    // Unexpected eContentType and missing eContent.
    let mut wrong_ect_sd = signed_data.clone();
    wrong_ect_sd.encap_content_info.econtent_type = ID_SIGNED_DATA;
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&wrong_ect_sd), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::UnexpectedEncapsulatedContentType(ID_SIGNED_DATA))
    );

    let mut missing_econtent_sd = signed_data.clone();
    missing_econtent_sd.encap_content_info.econtent = None;
    assert_eq!(
        verify_time_stamp_token(
            &encode_signed_data(&missing_econtent_sd),
            dummy_sig,
            pes_cert,
            roots,
        ),
        Err(TimeStampTokenError::MissingTstInfoContent)
    );

    // Unsupported TSTInfo version, invalid accuracy (millis = 0 or micros = 1000),
    // empty/duplicate TSTInfo extensions, and unhandled critical TSTInfo
    // extension.
    let encode_tst = |tst: &TstInfo<'_>| -> Vec<u8> {
        let der = tst.to_der().unwrap();
        let mut sd = signed_data.clone();
        sd.encap_content_info.econtent = Some(OctetStringRef::new(&der).unwrap());
        encode_signed_data(&sd)
    };

    let mut bad_ver_tst = tst_info.clone();
    bad_ver_tst.version = 2;
    assert_eq!(
        verify_time_stamp_token(&encode_tst(&bad_ver_tst), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::UnsupportedTstInfoVersion(2))
    );

    for bad_accuracy in [
        Accuracy { seconds: Some(1), millis: Some(0), micros: None },
        Accuracy { seconds: Some(1), millis: None, micros: Some(1000) },
    ] {
        let mut bad_acc_tst = tst_info.clone();
        bad_acc_tst.accuracy = Some(bad_accuracy);
        assert_eq!(
            verify_time_stamp_token(&encode_tst(&bad_acc_tst), dummy_sig, pes_cert, roots),
            Err(TimeStampTokenError::InvalidTstInfoAccuracy)
        );
    }

    let ext_oid = ObjectIdentifier::new_unwrap("1.2.3.4.5.6");
    let non_crit_ext = Extension {
        extn_id: ext_oid,
        critical: false,
        extn_value: OctetString::new([0x05, 0x00]).unwrap(),
    };
    for bad_exts in
        [Extensions::from(vec![]), Extensions::from(vec![non_crit_ext.clone(), non_crit_ext])]
    {
        let mut bad_ext_tst = tst_info.clone();
        bad_ext_tst.extensions = Some(bad_exts);
        assert!(matches!(
            verify_time_stamp_token(&encode_tst(&bad_ext_tst), dummy_sig, pes_cert, roots),
            Err(TimeStampTokenError::Der(_))
        ));
    }

    let mut crit_ext_tst = tst_info.clone();
    crit_ext_tst.extensions = Some(Extensions::from(vec![Extension {
        extn_id: ext_oid,
        critical: true,
        extn_value: OctetString::new([0x05, 0x00]).unwrap(),
    }]));
    assert_eq!(
        verify_time_stamp_token(&encode_tst(&crit_ext_tst), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::UnhandledCriticalTstInfoExtension(ext_oid))
    );

    // Missing SignerInfo, multiple SignerInfos, and invalid SignerInfo version.
    let mut no_si_sd = signed_data.clone();
    no_si_sd.signer_infos = SetOfVec::default();
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&no_si_sd), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::MissingSignerInfo)
    );

    let si_0 = signed_data.signer_infos.get(0).unwrap().clone();
    let mut si_1 = si_0.clone();
    si_1.version = 3;
    let mut multi_si_sd = signed_data.clone();
    multi_si_sd.signer_infos = SetOfVec::try_from(vec![si_0.clone(), si_1.clone()]).unwrap();
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&multi_si_sd), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::MultipleSignerInfos)
    );

    let mut bad_si_ver_sd = signed_data.clone();
    bad_si_ver_sd.signer_infos = SetOfVec::try_from(vec![si_1]).unwrap();
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&bad_si_ver_sd), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::InvalidSignerInfoVersion(3))
    );

    // Invalid parameters on SignerInfo.digest_algorithm report
    // InvalidDigestAlgorithmParameters even when SignedData.digest_algorithms
    // contains the same AlgorithmIdentifierOwned; missing entry in
    // SignedData.digest_algorithms reports DigestAlgorithmNotInSignedData.
    let bad_digest_alg = AlgorithmIdentifierOwned {
        oid: ID_SHA_256,
        parameters: Some(Any::encode_from(&ID_SHA_256).unwrap()),
    };
    let mut bad_param_sd = signed_data.clone();
    let mut si_bad_param = si_0.clone();
    si_bad_param.digest_algorithm = bad_digest_alg.clone();
    bad_param_sd.digest_algorithms = SetOfVec::try_from(vec![bad_digest_alg]).unwrap();
    bad_param_sd.signer_infos = SetOfVec::try_from(vec![si_bad_param]).unwrap();
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&bad_param_sd), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::InvalidDigestAlgorithmParameters(ID_SHA_256))
    );

    let mut missing_da_sd = signed_data.clone();
    missing_da_sd.digest_algorithms =
        SetOfVec::try_from(vec![AlgorithmIdentifierOwned { oid: ID_SHA_256, parameters: None }])
            .unwrap();
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&missing_da_sd), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::DigestAlgorithmNotInSignedData(ID_SHA_384))
    );

    // Incompatible SignerInfo.signature_algorithm is rejected before inspecting
    // signedAttrs.
    let mut bad_sig_alg_sd = signed_data.clone();
    let mut si_bad_sig_alg = si_0.clone();
    si_bad_sig_alg.signature_algorithm = AlgorithmIdentifierOwned {
        oid: SHA_256_WITH_RSA_ENCRYPTION,
        parameters: Some(Any::null()),
    };
    si_bad_sig_alg.signed_attrs = None;
    bad_sig_alg_sd.signer_infos = SetOfVec::try_from(vec![si_bad_sig_alg]).unwrap();
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&bad_sig_alg_sd), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::IncompatibleDigestAndSignatureAlgorithms {
            digest_alg: ID_SHA_384,
            sig_alg: SHA_256_WITH_RSA_ENCRYPTION,
        })
    );

    // Missing signedAttrs.
    let mut no_attrs_sd = signed_data.clone();
    let mut si_no_attrs = si_0.clone();
    si_no_attrs.signed_attrs = None;
    no_attrs_sd.signer_infos = SetOfVec::try_from(vec![si_no_attrs]).unwrap();
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&no_attrs_sd), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::MissingSignedAttrs)
    );

    // TSTInfo.tsa name matching against tbsCertificate.subject and
    // SubjectAltName (RFC 3161 Section 2.4.2 & RFC 5280 Section 4.2.1.6).
    let subject_gn = GeneralName::DirectoryName(certs[0].tbs_certificate.subject.clone());
    let alt_gn = GeneralName::DirectoryName(certs[1].tbs_certificate.subject.clone());
    let empty_gn = GeneralName::DirectoryName(Name::default());
    assert_eq!(verify_tsa_name(&subject_gn, &certs[0]), Ok(()));
    assert_eq!(verify_tsa_name(&alt_gn, &certs[0]), Err(TimeStampTokenError::TsaNameMismatch));
    assert_eq!(verify_tsa_name(&empty_gn, &certs[0]), Err(TimeStampTokenError::TsaNameMismatch));

    let san_der = SubjectAltName(vec![alt_gn.clone()]).to_der().unwrap();
    let mut cert_with_san = certs[0].clone();
    cert_with_san.tbs_certificate.subject = Name::default();
    cert_with_san.tbs_certificate.extensions.as_mut().unwrap().push(Extension {
        extn_id: ID_CE_SUBJECT_ALT_NAME,
        critical: true,
        extn_value: OctetString::new(san_der).unwrap(),
    });
    assert_eq!(verify_tsa_name(&alt_gn, &cert_with_san), Ok(()));
    assert_eq!(
        verify_tsa_name(&empty_gn, &cert_with_san),
        Err(TimeStampTokenError::TsaNameMismatch)
    );
    assert_eq!(verify_signer_cert_extensions(&cert_with_san), Ok(()));

    let mut wrong_tsa_tst = tst_info;
    wrong_tsa_tst.tsa = Some(alt_gn);
    let wrong_tsa_der = wrong_tsa_tst.to_der().unwrap();
    let wrong_tsa_digest =
        OctetString::new(Sha384::from_contents(&wrong_tsa_der).as_ref()).unwrap();
    let mut updated_attrs = Attributes::new();
    for attr in si_0.signed_attrs.as_ref().unwrap().iter() {
        if attr.oid == ID_MESSAGE_DIGEST {
            updated_attrs
                .insert(make_attr(
                    ID_MESSAGE_DIGEST,
                    vec![Any::encode_from(&wrong_tsa_digest).unwrap()],
                ))
                .unwrap();
        } else {
            updated_attrs.insert(attr.clone()).unwrap();
        }
    }
    let mut si_wrong_tsa = si_0;
    si_wrong_tsa.signed_attrs = Some(updated_attrs);
    let mut wrong_tsa_sd = signed_data.clone();
    wrong_tsa_sd.encap_content_info.econtent = Some(OctetStringRef::new(&wrong_tsa_der).unwrap());
    wrong_tsa_sd.signer_infos = SetOfVec::try_from(vec![si_wrong_tsa]).unwrap();
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&wrong_tsa_sd), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::TsaNameMismatch)
    );

    // Candidate signer certificate resolution via `SigningCertificateV2`
    // (`verify_ess_cert_id`) runs before extension and chain checks:
    // - If the only candidate matching `sid` is `fake_candidate` (a CA certificate
    //   `certs[1]` lacking `id-kp-timeStamping` EKU whose issuer and serial are
    //   overwritten to match `certs[0]`), validation fails with
    //   `SigningCertificateMismatch` rather than
    //   `MissingTimeStampingExtendedKeyUsage`.
    // - When `fake_candidate` precedes the real signer certificate `certs[0]`,
    //   `verify_ess_cert_id` skips `fake_candidate` and resolves `certs[0]`
    //   (reaching `MessageImprintMismatch` when the intermediate chain
    //   `certs[1..3]` is present, or `UntrustedCertificateChain` when intermediates
    //   are omitted).
    let mut fake_candidate = certs[1].clone();
    fake_candidate.tbs_certificate.issuer = certs[0].tbs_certificate.issuer.clone();
    fake_candidate.tbs_certificate.serial_number = certs[0].tbs_certificate.serial_number.clone();

    let mut only_fake_sd = signed_data.clone();
    only_fake_sd.certificates = Some(vec![fake_candidate.clone()]);
    assert_eq!(
        verify_time_stamp_token(&encode_signed_data(&only_fake_sd), dummy_sig, pes_cert, roots),
        Err(TimeStampTokenError::SigningCertificateMismatch)
    );

    let mut fake_first_with_chain_sd = signed_data.clone();
    fake_first_with_chain_sd.certificates =
        Some(vec![fake_candidate.clone(), certs[0].clone(), certs[1].clone(), certs[2].clone()]);
    assert_eq!(
        verify_time_stamp_token(
            &encode_signed_data(&fake_first_with_chain_sd),
            dummy_sig,
            pes_cert,
            roots,
        ),
        Err(TimeStampTokenError::MessageImprintMismatch)
    );

    for candidate_pair in
        [vec![certs[0].clone(), fake_candidate.clone()], vec![fake_candidate, certs[0].clone()]]
    {
        let mut dup_sid_sd = signed_data.clone();
        dup_sid_sd.certificates = Some(candidate_pair);
        assert_eq!(
            verify_time_stamp_token(&encode_signed_data(&dup_sid_sd), dummy_sig, pes_cert, roots),
            Err(TimeStampTokenError::UntrustedCertificateChain)
        );
    }
}
