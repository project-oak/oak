//
// Copyright 2024 The Project Oak Authors
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

use std::eprintln;

use oak_sev_snp_attestation_report::AttestationReport;
use test_util::attestation_data::AttestationData;
use x509_cert::{
    certificate::{CertificateInner, Version},
    der::{Decode, DecodePem},
    Certificate,
};
use zerocopy::FromBytes;

use crate::{
    amd::{get_product, AmdProduct},
    x509::verify_cert_signature,
};

const ARK_MILAN_CERT_PEM: &str = include_str!("../../data/ark_milan.pem");
const ARK_GENOA_CERT_PEM: &str = include_str!("../../data/ark_genoa.pem");
const ARK_TURIN_CERT_PEM: &str = include_str!("../../data/ark_turin.pem");
const ASK_MILAN_CERT_PEM: &str = include_str!("../../data/ask_milan.pem");
const ASK_GENOA_CERT_PEM: &str = include_str!("../../data/ask_genoa.pem");
const ASK_TURIN_CERT_PEM: &str = include_str!("../../data/ask_turin.pem");

fn vcek_from_data(data: &AttestationData) -> CertificateInner {
    let cert = data.get_tee_certificate().expect("failed to load VCEK cert");
    Certificate::from_der(&cert).expect("could not parse VCEK cert")
}

fn load_vcek_milan() -> CertificateInner {
    vcek_from_data(&AttestationData::load_milan_oc_release())
}

fn load_vcek_genoa() -> CertificateInner {
    vcek_from_data(&AttestationData::load_genoa_oc())
}

fn load_vcek_turin() -> CertificateInner {
    vcek_from_data(&AttestationData::load_turin_oc())
}

// Verifies validity of a matching ARK, ASK certificate pair.
//
// Validate at least a subset of Appendix B.3 of
// https://www.amd.com/content/dam/amd/en/documents/epyc-technical-docs/programmer-references/55766_SEV-KM_API_Specification.pdf
// Ideally, we'd check everything listed there.
fn validate_ark_ask_certs(ark: &Certificate, ask: &Certificate) -> anyhow::Result<()> {
    anyhow::ensure!(ark.tbs_certificate.version == Version::V3, "unexpected version of ARK cert");
    anyhow::ensure!(ask.tbs_certificate.version == Version::V3, "unexpected version of ASK cert");

    verify_cert_signature(ark, ask)?;
    verify_cert_signature(ark, ark)
}

// Utility to print all extension in a certificate.
fn eprint_exts(cert: &Certificate) -> anyhow::Result<()> {
    for ext in cert
        .tbs_certificate
        .extensions
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("could not get extensions from cert"))?
    {
        eprintln!("cert ext id={} val={}", ext.extn_id, hex::encode(ext.extn_value.as_bytes()));
    }
    Ok(())
}

fn load_cert(path: &str) -> Certificate {
    Certificate::from_pem(path).expect("could not parse cert")
}

#[test]
fn print_all_milan_certs() {
    let ark = load_cert(ARK_MILAN_CERT_PEM);
    let ask = load_cert(ASK_MILAN_CERT_PEM);
    let vcek = load_vcek_milan();
    eprint_exts(&ark).expect("error");
    eprint_exts(&ask).expect("error");
    eprint_exts(&vcek).expect("error");
}

#[test]
fn milan_ark_signs_itself() {
    let ark = load_cert(ARK_MILAN_CERT_PEM);
    assert!(verify_cert_signature(&ark, &ark).is_ok());
}

#[test]
fn milan_ark_signs_ask() {
    let ark = load_cert(ARK_MILAN_CERT_PEM);
    let ask = load_cert(ASK_MILAN_CERT_PEM);
    assert!(verify_cert_signature(&ark, &ask).is_ok());
}

#[test]
fn milan_ask_signs_vcek() {
    let ask = load_cert(ASK_MILAN_CERT_PEM);
    let vcek = load_vcek_milan();
    assert!(verify_cert_signature(&ask, &vcek).is_ok());
}

#[test]
fn genoa_ask_signs_vcek() {
    let ask = load_cert(ASK_GENOA_CERT_PEM);
    let vcek = load_vcek_genoa();
    assert!(verify_cert_signature(&ask, &vcek).is_ok());
}

#[test]
fn turin_ask_signs_vcek() {
    let ask = load_cert(ASK_TURIN_CERT_PEM);
    let vcek = load_vcek_turin();
    assert!(verify_cert_signature(&ask, &vcek).is_ok());
}

#[test]
fn genoa_ark_signs_itself() {
    let ark = load_cert(ARK_GENOA_CERT_PEM);
    assert!(verify_cert_signature(&ark, &ark).is_ok());
}

#[test]
fn genoa_ark_signs_ask() {
    let ark = load_cert(ARK_GENOA_CERT_PEM);
    let ask = load_cert(ASK_GENOA_CERT_PEM);
    assert!(verify_cert_signature(&ark, &ask).is_ok());
}

#[test]
fn turin_ark_signs_itself() {
    let ark = load_cert(ARK_TURIN_CERT_PEM);
    assert!(verify_cert_signature(&ark, &ark).is_ok());
}

#[test]
fn turin_ark_signs_ask() {
    let ark = load_cert(ARK_TURIN_CERT_PEM);
    let ask = load_cert(ASK_TURIN_CERT_PEM);
    assert!(verify_cert_signature(&ark, &ask).is_ok());
}

#[test]
fn milan_ark_does_not_sign_vcek() {
    let ark = load_cert(ARK_MILAN_CERT_PEM);
    let vcek = load_vcek_milan();
    assert!(verify_cert_signature(&ark, &vcek).is_err());
}

// Negative tests just to double check that ARK does not sign ASK when the
// CPU model doesn't match.
#[test]
fn ark_does_not_sign_ask() {
    let arks = [ARK_MILAN_CERT_PEM, ARK_GENOA_CERT_PEM, ARK_TURIN_CERT_PEM];
    let asks = [ASK_MILAN_CERT_PEM, ASK_GENOA_CERT_PEM, ASK_TURIN_CERT_PEM];
    for (i, ark_path) in arks.iter().enumerate() {
        let ark = load_cert(ark_path);
        for (j, ask_path) in asks.iter().enumerate() {
            if i == j {
                continue;
            }
            let ask = load_cert(ask_path);
            assert!(verify_cert_signature(&ark, &ask).is_err());
        }
    }
}

#[test]
fn validate_milan() {
    let ark = load_cert(ARK_MILAN_CERT_PEM);
    let ask = load_cert(ASK_MILAN_CERT_PEM);
    assert!(validate_ark_ask_certs(&ark, &ask).is_ok());
}

#[test]
fn validate_genoa() {
    let ark = load_cert(ARK_GENOA_CERT_PEM);
    let ask = load_cert(ASK_GENOA_CERT_PEM);
    assert!(validate_ark_ask_certs(&ark, &ask).is_ok());
}

#[test]
fn validate_turin() {
    let ark = load_cert(ARK_TURIN_CERT_PEM);
    let ask = load_cert(ASK_TURIN_CERT_PEM);
    assert!(validate_ark_ask_certs(&ark, &ask).is_ok());
}

fn get_product_from_report(d: &AttestationData) -> AmdProduct {
    let report = AttestationReport::ref_from_bytes(
        &d.evidence.root_layer.as_ref().unwrap().remote_attestation_report,
    )
    .expect("invalid AMD attestation report");
    report.data.get_product()
}

fn print_report(label: &str, d: &AttestationData) {
    let report = AttestationReport::ref_from_bytes(
        &d.evidence.root_layer.as_ref().unwrap().remote_attestation_report,
    )
    .expect("invalid AMD attestation report");
    eprintln!("Attestation report: {} -----------------------------", label);
    eprintln!("Version      {:?}", report.data.version);
    eprintln!(
        "CPU ID       0x{:02x} 0x{:02x} 0x{:02x}",
        report.data.cpuid_fam_id, report.data.cpuid_mod_id, report.data.cpuid_step
    );
    eprintln!("Hardware ID  {}", hex::encode(report.data.chip_id));
    eprintln!(
        "Current  TCB {:?} - parsed: {:?}",
        report.data.current_tcb,
        report.data.get_current_tcb_version()
    );
    eprintln!(
        "Reported TCB {:?} - parsed: {:?}",
        report.data.reported_tcb,
        report.data.get_reported_tcb_version()
    );
    eprintln!("Measurement  {}", hex::encode(report.data.measurement));
    eprintln!("End {} ---------------------------------------------", label);
}

fn get_product_from_vcek(d: &AttestationData) -> AmdProduct {
    let vcek_cert = Certificate::from_der(
        &d.get_tee_certificate().expect("couldn't get VCEK cert from test data"),
    )
    .expect("couldn't parse VCEK cert");
    get_product(&vcek_cert).expect("couldn't get product from VCEK cert")
}

#[test]
fn print_all_reports() {
    print_report("load_cb", &AttestationData::load_cb());
    print_report("load_milan_oc_staging", &AttestationData::load_milan_oc_staging());
    print_report("load_milan_oc_release", &AttestationData::load_milan_oc_release());
    print_report("load_milan_rk_staging", &AttestationData::load_milan_rk_staging());
    print_report("load_milan_rk_release", &AttestationData::load_milan_rk_release());
    print_report("load_genoa_oc", &AttestationData::load_genoa_oc());
    print_report("load_turin_oc", &AttestationData::load_turin_oc());
}

#[test]
fn test_product_from_report_milan() {
    assert_eq!(
        get_product_from_report(&AttestationData::load_milan_oc_release()),
        AmdProduct::Milan
    );
    assert_eq!(
        get_product_from_report(&AttestationData::load_milan_oc_staging()),
        AmdProduct::Milan
    );
    assert_eq!(
        get_product_from_report(&AttestationData::load_milan_rk_release()),
        AmdProduct::Milan
    );
    assert_eq!(
        get_product_from_report(&AttestationData::load_milan_rk_staging()),
        AmdProduct::Milan
    );
}

// TODO: b/396666645 - Test fails. We are unable to distinguish Milan and Genoa
// from the attestation report :-(.
// #[test]
// fn test_product_from_report_genoa() {
//     assert_eq!(get_product_from_report(&AttestationData::load_genoa_oc()),
// AmdProduct::Genoa); }

#[test]
fn test_product_from_report_turin() {
    assert_eq!(get_product_from_report(&AttestationData::load_turin_oc()), AmdProduct::Turin);
}

#[test]
fn test_product_from_vcek_milan() {
    assert_eq!(get_product_from_vcek(&AttestationData::load_milan_oc_release()), AmdProduct::Milan);
    assert_eq!(get_product_from_vcek(&AttestationData::load_milan_oc_staging()), AmdProduct::Milan);
    assert_eq!(get_product_from_vcek(&AttestationData::load_milan_rk_release()), AmdProduct::Milan);
    assert_eq!(get_product_from_vcek(&AttestationData::load_milan_rk_staging()), AmdProduct::Milan);
}

#[test]
fn test_product_from_vcek_genoa() {
    assert_eq!(get_product_from_vcek(&AttestationData::load_genoa_oc()), AmdProduct::Genoa);
}

#[test]
fn test_product_from_vcek_turin() {
    assert_eq!(get_product_from_vcek(&AttestationData::load_turin_oc()), AmdProduct::Turin);
}
