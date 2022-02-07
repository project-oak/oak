//
// Copyright 2021 The Project Oak Authors
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

use assert_matches::assert_matches;
use serde_json::Value;
use std::fs;

#[test]
fn testing_rekor_verification() {
    // The following description from https://github.com/sigstore/rekor/blob/4fcdcaa58fd5263560a82978d781eb64f5c5f93c/openapi.yaml#L433-L476 is somewhat inaccurate.
    // # To verify the signedEntryTimestamp:
    // # 1. Remove the Verification object from the JSON Document
    // # 2. Canonicalize the remaining JSON document by following RFC 8785 rules
    // # 3. Verify the canonicalized payload and signedEntryTimestamp against rekor's public key
    //
    // One should note that the description of `signedEntryTimestamp` says that it is a "Signature over the logID, logIndex, body and integratedTime."
    // So the outer LogEntry must be discarded, and the `attestation` field must be excluded too.
    // Also note that `signedEntryTimestamp` is base64 encoded. So most likely it should first be decoded to a byte array.

    // load the log entry and endorsement files
    let endorsement_path = "testdata/endorsement.json";
    let log_entry_path = "testdata/logentry.json";
    let log_entry_no_verification_path = "testdata/logentry_no_verification.json";
    let rekor_public_key_path = "testdata/rekor_public_key.pem";

    let endorsement_content = fs::read(endorsement_path).expect("Couldn't read endorsement file.");
    let log_entry_content = fs::read(log_entry_path).expect("Couldn't read log entry file.");
    let log_entry_no_verification = fs::read(log_entry_no_verification_path)
        .expect("Couldn't read verification-less rekor log entry file.");
    let rekor_public_key =
        fs::read(rekor_public_key_path).expect("Couldn't read rekor public key file.");

    // verify signature in the log entry

    let v: Value =
        serde_json::from_slice(&log_entry_content).expect("could load log entry as json object.");
    assert_matches!(v, Value::Object(_));
    let signed_entry_timestamp = match v {
        Value::Object(obj) => {
            assert_eq!(obj.values().len(), 1);
            let obj = obj.values().next().unwrap();
            assert_eq!(obj["verification"].as_object().unwrap().len(), 2);
            obj["verification"]["signedEntryTimestamp"].clone()
        }
        _ => panic!("Json file does contain an object."),
    };

    eprintln!("signedEntryTimestamp: {}", signed_entry_timestamp);
    let signed_hash = signed_entry_timestamp.as_str().unwrap().as_bytes().to_vec();

    let rekor_pem_content =
        pem::parse(&rekor_public_key).expect("could not parse Rekor public key as pem");
    assert_eq!(rekor_pem_content.tag, "PUBLIC KEY");
    let public_key_der = rekor_pem_content.contents;

    // get sha256 hash of verification-less rekor entry:
    let hash = oak_sign::get_sha256_hex(&log_entry_no_verification)
        .as_bytes()
        .to_vec();

    let sig_bundle = oak_sign::SignatureBundle {
        public_key_der,
        signed_hash,
        hash,
    };

    // The verify fails, what could be wrong?
    // 1. The json is not canonicalized.
    // 2. The hash is not sha256.
    // 3. The public key is not correctly formatted.
    // 4. The signing algorithm is different.
    eprintln!("{:?}", sig_bundle.verify());

    // get to body of log entry
    // verify hash in the body is equal to the hash of the endorsement file.
    // verify signature in the body; using the public key (is the public key in the body the same as the one we have? Even if it is, it cannot be trusted)
    assert!(log_entry_content.len() != endorsement_content.len());
}
