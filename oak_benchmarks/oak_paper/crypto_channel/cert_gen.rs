//
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

use std::{fs::File, io::Write};

use openssl::{
    asn1::Asn1Time,
    hash::MessageDigest,
    pkey::{PKey, Private},
    rsa::Rsa,
    x509::{X509, X509Name},
};

fn generate_self_signed_cert() -> (X509, PKey<Private>) {
    let rsa = Rsa::generate(2048).unwrap();
    let pkey = PKey::from_rsa(rsa).unwrap();

    let mut name = X509Name::builder().unwrap();
    name.append_entry_by_text("CN", "localhost").unwrap();
    let name = name.build();

    let mut cert_builder = X509::builder().unwrap();
    cert_builder.set_version(2).unwrap();
    cert_builder.set_subject_name(&name).unwrap();
    cert_builder.set_issuer_name(&name).unwrap();
    cert_builder.set_pubkey(&pkey).unwrap();
    cert_builder.set_not_before(&Asn1Time::days_from_now(0).unwrap()).unwrap();
    cert_builder.set_not_after(&Asn1Time::days_from_now(365).unwrap()).unwrap();

    let context = cert_builder.x509v3_context(None, None);
    let san = openssl::x509::extension::SubjectAlternativeName::new()
        .dns("localhost")
        .build(&context)
        .unwrap();
    cert_builder.append_extension(san).unwrap();

    cert_builder.sign(&pkey, MessageDigest::sha256()).unwrap();
    let cert = cert_builder.build();

    (cert, pkey)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <output_file>", args[0]);
        std::process::exit(1);
    }
    let output_file = &args[1];
    let (cert, pkey) = generate_self_signed_cert();
    let mut file = File::create(output_file).expect("failed to create output file");
    file.write_all(&cert.to_pem().expect("failed to serialize cert to PEM"))
        .expect("failed to write cert to file");
    file.write_all(&pkey.private_key_to_pem_pkcs8().expect("failed to serialize pkey to PEM"))
        .expect("failed to write pkey to file");
}
