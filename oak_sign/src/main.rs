//
// Copyright 2020 The Project Oak Authors
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

//! An utility binary to sign Oak Wasm modules.
//!
//! Invoke with:
//!
//! ```shell
//! cargo run --manifest-path=oak_sign/Cargo.toml -- \
//!     generate \
//!     --private-key=<PRIVATE_KEY_FILE>.key \
//!     --public-key=<PUBLIC_KEY_FILE>.pem
//!
//! cargo run --manifest-path=oak_sign/Cargo.toml -- \
//!     sign \
//!     --private-key=<PRIVATE_KEY_FILE>.key \
//!     --module=<WASM_MODULE_FILE>.wasm \
//!     --signature=<SIGNATURE_FILE>.sign
//!
//! cargo run --manifest-path=oak_sign/Cargo.toml -- \
//!     verify \
//!     --module=<WASM_MODULE_FILE>.wasm \
//!     --signature=<SIGNATURE_FILE>.sign
//! ```

use anyhow::Context;
use log::info;
use pem::{encode, encode_many, parse, parse_many, Pem};
use ring::{
    rand,
    signature::{self, KeyPair},
};
use std::{
    collections::HashMap,
    fs::{read, write},
};
use structopt::StructOpt;

/// Command line options for the Oak sign.
#[derive(StructOpt, Clone)]
#[structopt(about = "Oak Sign")]
struct Opt {
    #[structopt(subcommand)]
    cmd: Command,
}

/// Available commands for the Oak sign.
#[derive(StructOpt, Clone)]
enum Command {
    Generate(Generate),
    Sign(Sign),
    Verify(Verify),
}

#[derive(StructOpt, Clone)]
#[structopt(about = "Generate Ed25519 key pair")]
struct Generate {
    #[structopt(long, help = "Output private key file path")]
    pub private_key: String,
    #[structopt(long, help = "Output public key file path")]
    pub public_key: String,
}

#[derive(StructOpt, Clone)]
#[structopt(about = "Sign Wasm module")]
struct Sign {
    #[structopt(long, help = "Input private key file path")]
    pub private_key: String,
    #[structopt(long, help = "Input Wasm module path")]
    pub module: String,
    #[structopt(long, help = "Output signature path")]
    pub signature: String,
}

#[derive(StructOpt, Clone)]
#[structopt(about = "Verify Wasm module signature")]
struct Verify {
    #[structopt(long, help = "Input signature path")]
    pub signature: String,
    #[structopt(long, help = "Input Wasm module path")]
    pub module: String,
}

// PEM file tags.
const PRIVATE_KEY_TAG: &str = "PRIVATE KEY";
const PUBLIC_KEY_TAG: &str = "PUBLIC KEY";
const SIGNATURE_TAG: &str = "SIGNATURE";

/// Creates a PEM structure for encoding.
fn create_pem(tag: &str, contents: &[u8]) -> Pem {
    Pem {
        tag: tag.to_string(),
        contents: contents.to_vec(),
    }
}

/// Main execution point for the Oak sign.
fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    match opt.cmd {
        Command::Generate(ref opt) => {
            // Generate key pair.
            let rng = rand::SystemRandom::new();
            let private_key_bytes = signature::Ed25519KeyPair::generate_pkcs8(&rng)
                .expect("Couldn't generate key pair");
            let key_pair = signature::Ed25519KeyPair::from_pkcs8(private_key_bytes.as_ref())
                .expect("Couldn't parse generated key pair");
            let public_key_bytes = key_pair.public_key();

            // Encode key pair in PEM format
            let private_key_pem = create_pem(PRIVATE_KEY_TAG, private_key_bytes.as_ref());
            let encoded_private_key = encode(&private_key_pem);

            let public_key_pem = create_pem(PUBLIC_KEY_TAG, public_key_bytes.as_ref());
            let encoded_public_key = encode(&public_key_pem);

            // Write key files.
            write(&opt.private_key, encoded_private_key)
                .with_context(|| format!("Couldn't write private key file {}", &opt.private_key))?;
            write(&opt.public_key, encoded_public_key)
                .with_context(|| format!("Couldn't write public key file {}", &opt.public_key))?;
            info!("Key pair generated successfully");
        }
        Command::Sign(ref opt) => {
            // Read input files.
            let private_key_file = read(&opt.private_key)
                .with_context(|| format!("Couldn't read private key file {}", &opt.private_key))?;
            let module_bytes = read(&opt.module)
                .with_context(|| format!("Couldn't Wasm module file {}", &opt.module))?;

            // Sign Wasm module
            let private_key_pem =
                parse(private_key_file).context("Couldn't parse PEM encoded private key file")?;
            let key_pair =
                signature::Ed25519KeyPair::from_pkcs8(&private_key_pem.contents.as_ref())
                    .expect("Couldn't parse PKCS encoded private key");
            let public_key_bytes = key_pair.public_key();
            let signature_bytes = key_pair.sign(&module_bytes);

            // Encode signature in PEM format
            let public_key_pem = create_pem(PUBLIC_KEY_TAG, public_key_bytes.as_ref());
            let signature_pem = create_pem(SIGNATURE_TAG, signature_bytes.as_ref());
            let encoded_signature = encode_many(&[public_key_pem, signature_pem]);

            // Write signature file.
            write(&opt.signature, &encoded_signature)
                .with_context(|| format!("Couldn't write signature file {}", &opt.signature))?;
            info!("Wasm module signed successfully");
        }
        Command::Verify(ref opt) => {
            // Read input files.
            let signature_file = read(&opt.signature)
                .with_context(|| format!("Couldn't read signature file {}", &opt.signature))?;
            let module_bytes = read(&opt.module)
                .with_context(|| format!("Couldn't Wasm module file {}", &opt.module))?;

            // Parse signature file.
            let signature_content =
                parse_many(signature_file)
                    .iter()
                    .fold(HashMap::new(), |mut content, entry| {
                        content.insert(entry.tag.to_string(), entry.contents.to_vec());
                        content
                    });
            let public_key_bytes = signature_content
                .get(PUBLIC_KEY_TAG)
                .context("Signature file doesn't contain public key")?;
            let signature_bytes = signature_content
                .get(SIGNATURE_TAG)
                .context("Signature file doesn't contain signature")?;

            // Verify Wasm module signature.
            let public_key =
                signature::UnparsedPublicKey::new(&signature::ED25519, public_key_bytes);
            public_key
                .verify(&module_bytes, &signature_bytes)
                .expect("Wasm module signature verification failed");
            info!("Wasm module signature verified successfully");
        }
    }
    Ok(())
}
