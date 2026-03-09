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
    x509::{X509, X509Name},
};

// This key is for test purposes only.
const STATIC_TEST_PRIVATE_KEY_PEM: &[u8] = b"-----BEGIN PRIVATE KEY-----\n\
MIIEvwIBADANBgkqhkiG9w0BAQEFAASCBKkwggSlAgEAAoIBAQDQw6Qv9kZr8v+V\n\
N2E+6NrcKndoB/Vb/aFO2PGpuJMERONumBJlBP0ahojmXmQ76GCH5nEfvPk7qy70\n\
igwDj6K2x6x/HautEm62OpE6KCa+BkVZ+W+9odb5rinEHTCum+ow7Kb3XoMCKpeB\n\
2vTxsGF/cSlrepqpmaFHT46WXV/BzqHBOAEaV4rm1pztZx3hiyLTOZLKdtsGVA8B\n\
1cFjKghcY9kRnIA6iuTwu++/JddPh1VX25D9oN/8hIQxm/dhkYog3hNndGxx3pIo\n\
KIyswp+bNkRi72LhhflCmpIZWx3qTS4W5lBYBJlvidI8AlVVBuzHILOvG+JZlIGh\n\
6T/mNbCBAgMBAAECggEAB2o3gfOZnzpvjQV9SP58zY6dlJ6ZvqV0zgfjF3/kiuWG\n\
fXZdyuRBOCi4opQOM9mGWjVbZcDwykeDgLCJijPXF+5iKFatsxVBROwyHdJww9WV\n\
r4MuTpo5uD8RITPXN5B2oju5l3YuKYzJOlXEVvRIlj329mgRp7367j07Z4hT/x5v\n\
CRVIJHYE0xVz/+AWP4rdjdzdrcdYoOKf6fheD1X+/UIWeMdwhytt8638rYrDGp/i\n\
EM2IZSPw7Bw+T20/IHcV9UciBBbDy4+ndCswENKxou9ExYVJtF3bcU9zSimu46QU\n\
sXTLvh8lObJUtxbgdrKEYpVZ/6L+zHNX6j/cEB22QQKBgQD1kiSkYfHzoi5z0cpR\n\
2DtLRSWXi8hVFardkYkvsMMHAICKGqAcfvQ/0EaUTZOFjVNvkypq3OboWx4Q/n1Y\n\
IzoxMrCkb2D3R09fd0nVIskjHs4KlXVpXFVxqoQFG9dJbQ7a3JBGaamzsmyoejGK\n\
4VYZe10zdBe4HsVdh/qknPHG8QKBgQDZoVW1cgViW5WJqNBj7bHuZ7tx7A70xZq5\n\
xdSiqoFdN5Y+dI/5GP3RaIAYfd4+I9024jzTdfMQ8nZ86fp2CJ8PpTmUxuKc6ixT\n\
nwK1cr2isGHE+YsbPSXF2bOPXq7aXWiFCygvDrpt/ZwII+fFMT0sznkstDZLVsFa\n\
h6jKolgikQKBgQDeUgSiXZnye+2aJWAJYL2tk1hJLt+bSBZ8qXmNl3W5LRcx8JDr\n\
u3PdIe4D7YeU7TGQXaeVP5A84+EAeaV42cuhJscM11juBb0yLIjHUMrP5N+cbVry\n\
nAku8rS6+02YyAce1Xg4hwiACxScIqQfm4mbYDgskPm4UwNTffvIc93fwQKBgQCU\n\
3IJf5mpAaRzUWKCSedgnltTki+9/BltbjzJvQenS9V7Twa9pV+rl/nEAT7hhEO8T\n\
x5SLoDZu9SqPLwyfCC6k6QOF/LStWJCRckbMDnwgeD2oGnlIXH8l4k+sVbuMqjAA\n\
MS1/Yreq3LqJ5uV2QMPzjhfcuDgbOHBxmDGgyYM3wQKBgQDUdDGZqDg0Vh6usEkz\n\
CsF9tVPq1bmtng3AO4nLbTYHNwpILXHU94hQA1OZbAY/ZqtDiJnfZM7PycDQH8Zt\n\
fd9aFvJYwvOopWuoO8cTslZIH4XuQy59XirMAaxnB9S1eDWcSg0IHitgS9r8hvxA\n\
crKXYtwtk4bTaYgs01TaUmTRmg==\n\
-----END PRIVATE KEY-----\n";

fn generate_self_signed_cert() -> (X509, PKey<Private>) {
    let pkey = PKey::private_key_from_pem(STATIC_TEST_PRIVATE_KEY_PEM).unwrap();

    let mut name = X509Name::builder().unwrap();
    name.append_entry_by_text("CN", "localhost").unwrap();
    let name = name.build();

    let mut cert_builder = X509::builder().unwrap();
    cert_builder.set_version(2).unwrap();
    cert_builder.set_subject_name(&name).unwrap();
    cert_builder.set_issuer_name(&name).unwrap();
    cert_builder.set_pubkey(&pkey).unwrap();

    // Fixed validity period for deterministic cert generation (2026-01-01 to
    // 2036-01-01).
    cert_builder.set_not_before(&Asn1Time::from_str("20260101000000Z").unwrap()).unwrap();
    cert_builder.set_not_after(&Asn1Time::from_str("20360101000000Z").unwrap()).unwrap();

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
