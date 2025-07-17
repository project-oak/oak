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

use std::fs;

use oak_file_utils::data_path;
use oak_proto_rust::oak::attestation::v1::Evidence;
use oak_tdx_quote::{QeCertificationData, TdxQuoteWrapper};
use prost::Message;
use x509_cert::der::DecodePem;

use super::{
    verify_ecdsa_cert_signature, verify_intel_tdx_quote_validity,
    verify_quote_cert_chain_and_extract_leaf, PCK_ROOT,
};

// TDX Oak Containers attestation
const OC_TDX_EVIDENCE_PATH: &str = "oak_attestation_verification/testdata/oc_evidence_tdx.binarypb";

// Loads a valid Intel TDX evidence instance for Oak Containers.
fn get_oc_evidence_tdx() -> Evidence {
    let serialized = fs::read(data_path(OC_TDX_EVIDENCE_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

fn get_evidence_quote_bytes() -> Vec<u8> {
    let evidence = get_oc_evidence_tdx();
    evidence.root_layer.expect("no root layer").remote_attestation_report
}

#[test]
fn pck_root_signs_itself() {
    let pck_root = x509_cert::Certificate::from_pem(PCK_ROOT).expect("could not parse cert");
    let result = verify_ecdsa_cert_signature(&pck_root, &pck_root);
    assert!(result.is_ok());
}

#[test]
fn pck_chain_validation_passes() {
    let quote_buffer = get_evidence_quote_bytes();
    let wrapper = TdxQuoteWrapper::new(quote_buffer.as_slice());
    let signature_data = wrapper.parse_signature_data().expect("signature data parsing failed");

    let report_certification =
        if let QeCertificationData::QeReportCertificationData(report_certification) =
            signature_data.certification_data
        {
            report_certification
        } else {
            panic!("signature data contains the wrong type of certification data");
        };

    let leaf = verify_quote_cert_chain_and_extract_leaf(&report_certification.certification_data)
        .expect("invalid certificate chain");
    assert_eq!(
        leaf.tbs_certificate.subject.to_string(),
        "C=US,ST=CA,L=Santa Clara,O=Intel Corporation,CN=Intel SGX PCK Certificate"
    );
}

#[test]
fn valid_tdx_quote_validation_passes() {
    let quote_buffer = get_evidence_quote_bytes();
    let wrapper = TdxQuoteWrapper::new(quote_buffer.as_slice());
    assert!(verify_intel_tdx_quote_validity(&wrapper).is_ok());
}

#[test]
fn tdx_quote_with_invalid_pck_chain_fails() {
    let mut quote_buffer = get_evidence_quote_bytes();
    // Change a character in the PEM-encoded PCK leaf cert
    // (`oak_tdx_quote::QeReportCertificationData::certification_data` which will be
    // parsed from bytes 1258..4939 of the evidence).
    quote_buffer[1299] = b'v';
    let wrapper = TdxQuoteWrapper::new(quote_buffer.as_slice());
    assert!(verify_intel_tdx_quote_validity(&wrapper).is_err());
}

#[test]
fn tdx_quote_with_invalid_qe_report_signature_fails() {
    let mut quote_buffer = get_evidence_quote_bytes();
    // Change a byte in the QE report signature
    // (`oak_tdx_quote::QeReportCertificationData::signature` which will be
    // parsed from bytes 1154..1218 of the evidence).
    quote_buffer[1210] = 0;
    let wrapper = TdxQuoteWrapper::new(quote_buffer.as_slice());
    assert!(verify_intel_tdx_quote_validity(&wrapper).is_err());
}

#[test]
fn tdx_quote_with_invalid_attestation_key_fails() {
    let mut quote_buffer = get_evidence_quote_bytes();
    // Change a byte in the attestation key
    // (`oak_tdx_quote::QuoteSignatureData::ecdsa_attestation_key` which will be
    // parsed from bytes 700..764 of the evidence).

    quote_buffer[701] = 0;
    let wrapper = TdxQuoteWrapper::new(quote_buffer.as_slice());
    assert!(verify_intel_tdx_quote_validity(&wrapper).is_err());
}

#[test]
fn tdx_quote_with_invalid_attestation_signature_fails() {
    let mut quote_buffer = get_evidence_quote_bytes();
    // Change a byte in the quote signature
    // (`oak_tdx_quote::QuoteSignatureData::quote_signature` which will be parsed
    // from bytes 636..700 of the evidence).
    quote_buffer[637] = 0;
    let wrapper = TdxQuoteWrapper::new(quote_buffer.as_slice());
    assert!(verify_intel_tdx_quote_validity(&wrapper).is_err());
}
