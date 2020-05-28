// Copyright 2017-2019 int08h LLC
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

//!
//! CLI used to encrypt and decrypt the Roughenough long-term key
//! using one of the KMS implementations
//!

#[macro_use]
extern crate log;

use clap::{App, Arg};

#[allow(unused_imports)]
use roughenough::kms::{EnvelopeEncryption, KmsProvider};
use roughenough::roughenough_version;

#[cfg(not(any(feature = "awskms", feature = "gcpkms")))]
fn encrypt_seed(_: &str, _: &str) {
    // main() will exit if kms support is not enabled, making this unreachable
    unreachable!()
}

#[cfg(any(feature = "awskms", feature = "gcpkms"))]
fn encrypt_seed(kms_key: &str, hex_seed: &str) {
    let kms_client = get_kms(kms_key);

    let plaintext_seed = hex::decode(hex_seed).expect("Error decoding hex seed value");

    if plaintext_seed.len() != 32 {
        panic!("Seed must be 32 bytes long; provided seed is {}", plaintext_seed.len());
    }

    match EnvelopeEncryption::encrypt_seed(&kms_client, &plaintext_seed) {
        Ok(encrypted_blob) => {
            println!("kms_protection: \"{}\"", kms_key);
            println!("seed: {}", hex::encode(&encrypted_blob));
        }
        Err(e) => {
            error!("Error: {:?}", e);
        }
    }
}

#[cfg(not(any(feature = "awskms", feature = "gcpkms")))]
fn decrypt_blob(_: &str, _: &str) {
    // main() will exit if kms support is not enabled, making this unreachable
    unreachable!()
}

#[cfg(any(feature = "awskms", feature = "gcpkms"))]
fn decrypt_blob(kms_key: &str, hex_blob: &str) {
    let kms_client = get_kms(kms_key);
    let ciphertext = hex::decode(hex_blob).expect("Error decoding hex blob value");

    match EnvelopeEncryption::decrypt_seed(&kms_client, ciphertext.as_ref()) {
        Ok(plaintext) => {
            println!("{}", hex::encode(plaintext));
        }
        Err(e) => {
            error!("Error: {:?}", e);
        }
    }
}

#[cfg(feature = "awskms")]
fn get_kms(kms_key: &str) -> impl KmsProvider {
    use roughenough::kms::AwsKms;
    AwsKms::from_arn(kms_key).unwrap()
}

#[cfg(feature = "gcpkms")]
fn get_kms(kms_key: &str) -> impl KmsProvider {
    use roughenough::kms::GcpKms;
    GcpKms::from_resource_id(kms_key).unwrap()
}

#[allow(unused_variables)]
pub fn main() {
    use log::Level;

    simple_logger::init_with_level(Level::Info).unwrap();

    let matches = App::new("roughenough-kms")
        .version(roughenough_version().as_ref())
        .long_about("Encrypt and decrypt Roughenough long-term server seeds using a KMS")
        .arg(
            Arg::with_name("KEY_ID")
                .short("k")
                .long("kms-key")
                .takes_value(true)
                .required(true)
                .help("Identity of the KMS key to be used")
        ).arg(
            Arg::with_name("DECRYPT")
                .short("d")
                .long("decrypt")
                .takes_value(true)
                .required(false)
                .help("Previously encrypted blob to decrypt to plaintext"),
        ).arg(
            Arg::with_name("SEED")
                .short("s")
                .long("seed")
                .takes_value(true)
                .required(false)
                .help("32 byte hex seed for the server's long-term identity"),
        ).get_matches();

    if !(cfg!(feature = "gcpkms") || cfg!(feature = "awskms")) {
        warn!("KMS support was not compiled into this build; nothing to do.");
        warn!("See the Roughenough documentation for information on KMS support.");
        warn!("  https://github.com/int08h/roughenough/blob/master/doc/OPTIONAL-FEATURES.md");
        return
    }

    let kms_key = matches.value_of("KEY_ID").expect("Invalid KMS key id");

    if matches.is_present("SEED") {
        let hex_seed = matches.value_of("SEED").expect("Invalid seed value");
        encrypt_seed(kms_key, hex_seed);

    } else if matches.is_present("DECRYPT") {
        let hex_blob = matches.value_of("DECRYPT").expect("Invalid blob value");
        decrypt_blob(kms_key, hex_blob);

    } else {
        error!("Neither seed encryption (-s) or blob decryption (-d) was specified.");
        error!("One of them is required.");
    }
}
