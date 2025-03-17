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

use anyhow::Context;
use clap::Parser;
use oak_attestation_verification::{convert_pem_to_raw, verify_endorsement};
use oak_proto_rust::oak::attestation::v1::{
    endorsement::Format, verifying_key_reference_value, ClaimReferenceValue, Endorsement,
    EndorsementReferenceValue, KeyType, Signature, SignedEndorsement, SkipVerification,
    VerifyingKey, VerifyingKeyReferenceValue, VerifyingKeySet,
};

// The key ID for the endorser key is meaningless in this setting, just make
// sure we use the same number in signed endorsement and reference values.
const KEY_ID: u32 = 1;

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

    let now_utc_millis: i64 = match p.now_utc_millis {
        None => SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("could not get current time")
            .as_millis(),
        Some(millis) => millis.try_into().unwrap(),
    }
    .try_into()
    .unwrap();
    let endorsement = fs::read(p.endorsement).expect("couldn't read endorsement");
    let signature = fs::read(p.signature).expect("couldn't read signature");
    let log_entry = match p.log_entry {
        None => Vec::new(),
        Some(path_buf) => fs::read(path_buf).expect("couldn't read log entry"),
    };
    let subject = match p.subject {
        None => Vec::new(),
        Some(path_buf) => fs::read(path_buf).expect("couldn't read subject"),
    };

    let endorser_public_key_pem =
        fs::read_to_string(p.endorser_public_key).expect("couldn't read endorser public key");
    let endorser_public_key = convert_pem_to_raw(endorser_public_key_pem.as_str())
        .expect("failed to convert endorser key");

    let signed_endorsement = SignedEndorsement {
        endorsement: Some(Endorsement {
            format: Format::EndorsementFormatJsonIntoto.into(),
            serialized: endorsement.to_vec(),
            subject: subject.clone(),
        }),
        signature: Some(Signature { key_id: KEY_ID, raw: signature.to_vec() }),
        rekor_log_entry: log_entry.clone(),
    };
    let endorser_key = VerifyingKey {
        r#type: KeyType::EcdsaP256Sha256.into(),
        key_id: KEY_ID,
        raw: endorser_public_key.clone(),
    };
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
