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

use core::assert_eq;

use oak_tdx_quote::{QeCertificationData, TdxQuoteWrapper};
use sha2::{Digest, Sha384};
use test_util::AttestationData;
use x509_cert::der::DecodePem;

use super::{
    verify_ecdsa_cert_signature, verify_intel_tdx_quote_validity,
    verify_quote_cert_chain_and_extract_leaf, RtmrEmulator, PCK_ROOT,
};

fn get_evidence_quote_bytes() -> Vec<u8> {
    let d = AttestationData::load_tdx_oc();
    d.evidence.root_layer.expect("no root layer").remote_attestation_report
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

#[test]
fn test_extend_rtmr_once() {
    // Example encoded event when running Stage 0 on a TDX machine. Generated
    // 2025-09-26.
    let encoded_event = [
        10u8, 6, 83, 116, 97, 103, 101, 48, 18, 135, 3, 10, 57, 116, 121, 112, 101, 46, 103, 111,
        111, 103, 108, 101, 97, 112, 105, 115, 46, 99, 111, 109, 47, 111, 97, 107, 46, 97, 116,
        116, 101, 115, 116, 97, 116, 105, 111, 110, 46, 118, 49, 46, 83, 116, 97, 103, 101, 48, 77,
        101, 97, 115, 117, 114, 101, 109, 101, 110, 116, 115, 18, 201, 2, 10, 32, 90, 92, 212, 43,
        148, 113, 170, 223, 150, 220, 45, 36, 7, 217, 220, 187, 17, 101, 194, 140, 126, 234, 26,
        11, 78, 156, 114, 207, 6, 35, 187, 186, 18, 32, 249, 208, 88, 66, 71, 180, 108, 194, 52,
        168, 98, 170, 140, 208, 135, 101, 179, 132, 5, 2, 34, 83, 167, 139, 154, 241, 137, 196,
        206, 219, 228, 71, 26, 32, 35, 210, 113, 214, 46, 236, 158, 219, 200, 248, 116, 36, 190,
        116, 17, 105, 229, 96, 65, 221, 8, 244, 5, 231, 101, 78, 16, 69, 79, 71, 34, 27, 34, 32,
        159, 20, 82, 0, 196, 17, 174, 178, 179, 240, 40, 33, 191, 199, 231, 223, 188, 135, 159,
        185, 218, 133, 102, 180, 79, 223, 78, 252, 153, 117, 81, 233, 42, 32, 27, 42, 229, 140, 58,
        54, 176, 61, 221, 25, 56, 182, 175, 176, 57, 131, 106, 251, 101, 147, 48, 125, 105, 117,
        190, 124, 174, 249, 200, 164, 42, 104, 50, 156, 1, 99, 111, 110, 115, 111, 108, 101, 61,
        116, 116, 121, 83, 48, 32, 112, 97, 110, 105, 99, 61, 45, 49, 32, 101, 97, 114, 108, 121,
        99, 111, 110, 61, 117, 97, 114, 116, 44, 105, 111, 44, 48, 120, 51, 70, 56, 32, 98, 114,
        100, 46, 114, 100, 95, 110, 114, 61, 49, 32, 98, 114, 100, 46, 114, 100, 95, 115, 105, 122,
        101, 61, 51, 48, 55, 50, 48, 48, 48, 32, 98, 114, 100, 46, 109, 97, 120, 95, 112, 97, 114,
        116, 61, 49, 32, 105, 112, 61, 49, 48, 46, 48, 46, 50, 46, 49, 53, 58, 58, 58, 50, 53, 53,
        46, 50, 53, 53, 46, 50, 53, 53, 46, 48, 58, 58, 101, 116, 104, 48, 58, 111, 102, 102, 32,
        110, 101, 116, 46, 105, 102, 110, 97, 109, 101, 115, 61, 48, 32, 108, 111, 103, 108, 101,
        118, 101, 108, 61, 55,
    ];
    // Example value of RTMR 2 when Stage 0 extended it using the encoded event log
    // entry above. Generated on 2025-09-26.
    let expected = [
        199u8, 145, 101, 39, 103, 232, 29, 124, 234, 183, 103, 160, 142, 59, 136, 59, 20, 147, 31,
        141, 114, 70, 3, 174, 179, 117, 107, 227, 62, 94, 172, 36, 78, 95, 115, 29, 34, 112, 115,
        225, 111, 195, 201, 183, 152, 189, 97, 41,
    ];

    let mut rtmr = RtmrEmulator::new();
    rtmr.extend(&Sha384::digest(encoded_event.as_slice()).into());
    let actual = rtmr.get_state();

    assert_eq!(actual.len(), expected.len(), "slice lengths do not match");
    assert_eq!(
        actual, expected,
        "the calculated value for RTMR2 does not match the value from the quote"
    );
}

#[test]
fn test_extend_rtmr_three_times() {
    let event_1 = b"Encoded Event 1";
    let event_2 = b"Encoded Event 2";
    let event_3 = b"Encoded Event 3";
    let expected = [
        103u8, 53, 192, 142, 67, 91, 53, 80, 231, 237, 41, 97, 252, 39, 71, 192, 217, 126, 121,
        144, 160, 105, 210, 118, 130, 139, 238, 105, 161, 191, 241, 221, 211, 115, 247, 96, 102,
        128, 0, 45, 13, 211, 182, 193, 21, 90, 18, 39,
    ];

    let mut rtmr = RtmrEmulator::new();
    rtmr.extend(&Sha384::digest(event_1.as_slice()).into());
    rtmr.extend(&Sha384::digest(event_2.as_slice()).into());
    rtmr.extend(&Sha384::digest(event_3.as_slice()).into());
    let actual = rtmr.get_state();

    assert_eq!(actual.len(), expected.len(), "slice lengths do not match");
    assert_eq!(
        actual, expected,
        "the calculated value for RTMR2 does not match the value from the quote"
    );
}
