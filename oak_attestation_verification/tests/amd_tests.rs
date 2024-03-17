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

use oak_attestation_verification::amd::{validate_ark_ask_certs, verify_cert_signature};
use x509_cert::{der::DecodePem, Certificate};

const ARK_MILAN_CERT_PEM: &str = include_str!("../data/ark_milan.pem");
const ARK_GENOA_CERT_PEM: &str = include_str!("../data/ark_genoa.pem");
const ASK_MILAN_CERT_PEM: &str = include_str!("../data/ask_milan.pem");
const ASK_GENOA_CERT_PEM: &str = include_str!("../data/ask_genoa.pem");
const VCEK_MILAN_CERT_PEM: &str = include_str!("../testdata/oc_vcek_milan.pem");

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

#[test]
fn print_all_certs() {
    let ark = Certificate::from_pem(ARK_MILAN_CERT_PEM).expect("could not parse cert");
    let ask = Certificate::from_pem(ASK_MILAN_CERT_PEM).expect("could not parse cert");
    let vcek = Certificate::from_pem(VCEK_MILAN_CERT_PEM).expect("could not parse cert");
    eprint_exts(&ark).expect("error");
    eprint_exts(&ask).expect("error");
    eprint_exts(&vcek).expect("error");
}

#[test]
fn milan_ark_signs_itself() {
    let ark = Certificate::from_pem(ARK_MILAN_CERT_PEM).expect("could not parse cert");
    assert!(verify_cert_signature(&ark, &ark).is_ok());
}

#[test]
fn milan_ark_signs_ask() {
    let ark = Certificate::from_pem(ARK_MILAN_CERT_PEM).expect("could not parse cert");
    let ask = Certificate::from_pem(ASK_MILAN_CERT_PEM).expect("could not parse cert");
    assert!(verify_cert_signature(&ark, &ask).is_ok());
}

#[test]
fn milan_ask_signs_vcek() {
    let ask = Certificate::from_pem(ASK_MILAN_CERT_PEM).expect("could not parse cert");
    let vcek = Certificate::from_pem(VCEK_MILAN_CERT_PEM).expect("could not parse cert");
    assert!(verify_cert_signature(&ask, &vcek).is_ok());
}

#[test]
fn genoa_ark_signs_itself() {
    let ark = x509_cert::Certificate::from_pem(ARK_GENOA_CERT_PEM).expect("could not parse cert");
    assert!(verify_cert_signature(&ark, &ark).is_ok());
}

#[test]
fn genoa_ark_signs_ask() {
    let ark = Certificate::from_pem(ARK_GENOA_CERT_PEM).expect("could not parse cert");
    let ask = Certificate::from_pem(ASK_GENOA_CERT_PEM).expect("could not parse cert");
    assert!(verify_cert_signature(&ark, &ask).is_ok());
}

// Negative test just to double check.
#[test]
fn genoa_ark_does_not_sign_milan_ask() {
    let ark = Certificate::from_pem(ARK_GENOA_CERT_PEM).expect("could not parse cert");
    let ask = Certificate::from_pem(ASK_MILAN_CERT_PEM).expect("could not parse cert");
    assert!(verify_cert_signature(&ark, &ask).is_err());
}

// Negative test just to double check.
#[test]
fn milan_ark_does_not_sign_vcek() {
    let ark = Certificate::from_pem(ARK_MILAN_CERT_PEM).expect("could not parse cert");
    let vcek = Certificate::from_pem(VCEK_MILAN_CERT_PEM).expect("could not parse cert");
    assert!(verify_cert_signature(&ark, &vcek).is_err());
}

#[test]
fn validate_milan() {
    let ark = Certificate::from_pem(ARK_MILAN_CERT_PEM).expect("could not parse cert");
    let ask = Certificate::from_pem(ASK_MILAN_CERT_PEM).expect("could not parse cert");
    assert!(validate_ark_ask_certs(&ark, &ask).is_ok());
}

#[test]
fn validate_genoa() {
    let ark = Certificate::from_pem(ARK_GENOA_CERT_PEM).expect("could not parse cert");
    let ask = Certificate::from_pem(ASK_GENOA_CERT_PEM).expect("could not parse cert");
    assert!(validate_ark_ask_certs(&ark, &ask).is_ok());
}
