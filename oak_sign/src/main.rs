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

//! An utility binary to sign files using Ed25519.
//! https://ed25519.cr.yp.to.
//!
//! Invoke with:
//!
//! ```shell
//! cargo run --manifest-path=oak_sign/Cargo.toml -- \
//!     generate \
//!     --private-key=<PRIVATE_KEY_FILE>.key \
//!     --public-key=<PUBLIC_KEY_FILE>.pub
//!
//! cargo run --manifest-path=oak_sign/Cargo.toml -- \
//!     sign \
//!     --private-key=<PRIVATE_KEY_FILE>.key \
//!     --input-file=<INPUT_FILE> \
//!     --signature-file=<SIGNATURE_FILE>.sign
//!
//! cargo run --manifest-path=oak_sign/Cargo.toml -- \
//!     verify \
//!     --signature-file=<SIGNATURE_FILE>.sign
//! ```

use anyhow::{anyhow, Context};
use log::info;
use oak_sign::{
    read_pem_file, write_pem_file, KeyPair, SignatureBundle, PRIVATE_KEY_TAG, PUBLIC_KEY_TAG,
};
use structopt::StructOpt;

#[cfg(test)]
mod tests;

/// Command line options for `oak_sign`.
#[derive(StructOpt, Clone)]
#[structopt(about = "Oak Sign")]
struct Opt {
    #[structopt(subcommand)]
    cmd: Command,
}

/// Available commands for `oak_sign`.
#[derive(StructOpt, Clone)]
enum Command {
    Generate(Generate),
    Sign(Sign),
    Verify(Verify),
}

#[derive(StructOpt, Clone)]
#[structopt(about = "Generate Ed25519 key pair")]
struct Generate {
    #[structopt(long, help = "Output PEM encoded Ed25519 private key file path")]
    pub private_key: String,
    #[structopt(long, help = "Output PEM encoded Ed25519 public key file path")]
    pub public_key: String,
}

#[derive(StructOpt, Clone)]
#[structopt(about = "Sign input file")]
struct Sign {
    #[structopt(long, help = "Input PEM encoded Ed25519 private key file path")]
    pub private_key: String,
    #[structopt(
        long,
        conflicts_with = "input_string",
        help = "Input file path (Exactly one between `input_file` and `input_string` must be specified)"
    )]
    pub input_file: Option<String>,
    #[structopt(long, conflicts_with = "input_file", help = "Input string")]
    pub input_string: Option<String>,
    #[structopt(long, help = "Output PEM encoded Ed25519 signature file path")]
    pub signature_file: String,
}

#[derive(StructOpt, Clone)]
#[structopt(about = "Verify input file signature")]
struct Verify {
    #[structopt(long, help = "Input PEM encoded Ed25519 signature file path")]
    pub signature_file: String,
}

/// Main execution point for `oak_sign`.
fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    match opt.cmd {
        Command::Generate(ref opt) => {
            let key_pair = KeyPair::generate()?;
            write_pem_file(
                &opt.private_key,
                PRIVATE_KEY_TAG,
                &key_pair.key_pair_pkcs_8(),
            )?;
            write_pem_file(&opt.public_key, PUBLIC_KEY_TAG, &key_pair.public_key_der()?)?;
            info!("Key pair generated successfully");
        }
        Command::Sign(ref opt) => {
            let private_key = read_pem_file(&opt.private_key)?;
            let key_pair = KeyPair::parse(&private_key)?;
            let input = match (&opt.input_file, &opt.input_string) {
                (Some(input_file), None) => std::fs::read(&input_file)
                    .with_context(|| format!("Couldn't read input file {}", &input_file)),
                (None, Some(input_string)) => {
                    if input_string.is_empty() {
                        Err(anyhow!("`input_string` must have non-zero length"))
                    } else {
                        Ok(input_string.as_bytes().to_vec())
                    }
                }
                _ => Err(anyhow!(
                    "Exactly one between `input_file` and `input_string` must be specified"
                )),
            }?;
            let signature = SignatureBundle::create(&input, &key_pair)?;
            signature.to_pem_file(&opt.signature_file)?;
            info!("Input file signed successfully");
        }
        Command::Verify(ref opt) => {
            let signature = SignatureBundle::from_pem_file(&opt.signature_file)?;
            signature.verify()?;
            info!("Input file signature verified successfully");
        }
    }
    Ok(())
}
