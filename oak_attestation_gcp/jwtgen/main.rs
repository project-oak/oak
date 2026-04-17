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

use std::{
    fs,
    io::{self, Read},
};

use anyhow::Context;
use base64::{
    Engine,
    engine::general_purpose::{STANDARD, URL_SAFE_NO_PAD},
};
use clap::Parser;
use rsa::{
    pkcs1v15::SigningKey,
    pkcs8::DecodePrivateKey,
    sha2::Sha256,
    signature::{SignatureEncoding, Signer},
};
use serde_json::Value;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long, value_parser = parse_key_at)]
    signing_key: SigningKey<Sha256>,
    #[arg(long, value_parser = parse_cert_at)]
    // note: we must use the fully qualified Vec or clap will fail at runtime
    signing_cert: std::vec::Vec<u8>,
    // note: we must use the fully qualified Vec or clap will fail at runtime
    #[arg(long, value_parser = parse_cert_at)]
    root_ca_cert: std::vec::Vec<u8>,
}

fn parse_key_at(path: &str) -> anyhow::Result<SigningKey<Sha256>> {
    let data = &fs::read_to_string(path).context(format!("failed to read signing key: {path}"))?;
    SigningKey::<Sha256>::from_pkcs8_pem(data)
        .map_err(|_| anyhow::anyhow!("failed to parse signing key: {}", path))
}

fn parse_cert_at(path: &str) -> anyhow::Result<std::vec::Vec<u8>> {
    let data = &fs::read_to_string(path).context(format!("failed to read cert file: {path}"))?;
    let cert = pem::parse(data).context(format!("failed to parse cert file: {path}"))?;
    Ok(cert.into_contents())
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let x5c = vec![STANDARD.encode(&args.signing_cert), STANDARD.encode(&args.root_ca_cert)];

    let header = serde_json::json!({
        "alg": "RS256",
        "typ": "JWT",
        "x5c": x5c,
    });

    let mut buffer = String::new();
    io::stdin().read_to_string(&mut buffer)?;
    let claims: Value = serde_json::from_str(&buffer)?;

    let header_b64 = URL_SAFE_NO_PAD.encode(serde_json::to_string(&header)?);
    let claims_b64 = URL_SAFE_NO_PAD.encode(serde_json::to_string(&claims)?);

    let message = format!("{}.{}", header_b64, claims_b64);

    let signature = args.signing_key.sign(message.as_bytes());
    let signature_b64 = URL_SAFE_NO_PAD.encode(signature.to_vec());

    print!("{}.{}.{}", header_b64, claims_b64, signature_b64);

    Ok(())
}
