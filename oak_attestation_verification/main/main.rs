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

// Thin wrapper around oak_attestation_verification::verify_endorsement().

use std::{
    fs,
    path::PathBuf,
    time::{SystemTime, UNIX_EPOCH},
};

use anyhow::{Context, Result};
use clap::Parser;
use oak_attestation_verification::{convert_pem_to_raw, verify_endorsement};
use oak_proto_rust::oak::attestation::v1::{
    verifying_key_reference_value, ClaimReferenceValue, EndorsementReferenceValue, KeyType,
    SkipVerification, VerifyingKey, VerifyingKeyReferenceValue, VerifyingKeySet,
};

use crate::loader::EndorsementLoader;

mod loader;

// The key ID for the endorser key is meaningless in this setting, just make
// sure we use the same number in signed endorsement and reference values.
pub const KEY_ID: u32 = 1;

#[derive(Parser, Debug)]
pub struct Params {
    #[arg(long, help = "Time in milliseconds UTC since Unix Epoch or current time if not set.")]
    pub now_utc_millis: Option<i64>,

    #[arg(long, value_parser = path_exists, help = "Path to the endorsement.json to verify.")]
    pub endorsement: PathBuf,

    #[arg(long, value_parser = path_exists, help = "Path to the subject if needed for the verification.")]
    pub subject: Option<PathBuf>,

    #[arg(long, value_parser = path_exists, help = "Path to the endorsement.json.sig to verify.")]
    pub signature: PathBuf,

    #[arg(long, value_parser = path_exists, help = "Path to the logentry.json to verify, if available.")]
    pub log_entry: Option<PathBuf>,

    #[arg(long, value_parser = path_exists, help = "Path to the public key to verify.")]
    pub endorser_public_key: PathBuf,
}

fn path_exists(param: &str) -> Result<PathBuf, String> {
    let path = PathBuf::from(param);
    if !fs::metadata(param).map_err(|err| err.to_string())?.is_file() {
        Err(String::from("path does not represent a file"))
    } else {
        Ok(path)
    }
}

fn main() {
    let p = Params::parse();

    let endorsement_loader = loader::FileEndorsementLoaderBuilder::default()
        .endorsement_path(p.endorsement)
        .signature_path(p.signature)
        .log_entry_path(p.log_entry)
        .subject_path(p.subject)
        .build()
        .expect("Failed to build endorsement loader");

    let signed_endorsement =
        endorsement_loader.load_endorsement().expect("Failed to load endorsement");

    let now_utc_millis: i64 = p.now_utc_millis.unwrap_or_else(|| {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .with_context(|| "Failed to get UNIX_EPOCH from SystemTime::now()")
            .and_then(|d| {
                d.as_millis().try_into().with_context(|| "Failed to downcast duration to i64")
            })
            .expect("failed to convert time to milliseconds")
    });

    let endorser_key = fs::read_to_string(&p.endorser_public_key)
        .with_context(|| {
            format!("Failed to read endorser public key from {}", p.endorser_public_key.display())
        })
        .and_then(|pem| convert_pem_to_raw(pem.as_str()))
        .map(|raw| VerifyingKey { r#type: KeyType::EcdsaP256Sha256.into(), key_id: KEY_ID, raw })
        .expect("Could not create endorser key");

    let ref_values = EndorsementReferenceValue {
        endorser: Some(VerifyingKeySet { keys: [endorser_key].to_vec(), ..Default::default() }),
        required_claims: Some(ClaimReferenceValue { claim_types: vec![] }),
        rekor: Some(VerifyingKeyReferenceValue {
            r#type: Some(verifying_key_reference_value::Type::Skip(SkipVerification {})),
        }),
        ..Default::default()
    };
    let result = verify_endorsement(now_utc_millis, &signed_endorsement, &ref_values)
        .context("verifying endorsement");
    if result.is_err() {
        panic!("❌ Verification failed: {:?}", result.err().unwrap());
    }

    println!("✅ OK");
}
