//
// Copyright 2022 The Project Oak Authors
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

use crate::rekor::*;
use std::fs;

#[test]
fn test_verify_rekor_log_entry() {
    // Example endorsement file corresponding to the provenance file in
    // https://github.com/project-oak/transparent-release/blob/main/testdata/provenances/15dc16c42a4ac9ed77f337a4a3065a63e444c29c18c8cf69d6a6b4ae678dca5c.json
    let endorsement_path = "../testdata/endorsement.json";

    // LogEntry downloaded from
    // https://rekor.sigstore.dev/api/v1/log/entries/bb05be1bd813f8afb7b77b2d9f7be5ae25b396d111c7a26a04b785c48c277372.
    // This LogEntry was created by sining the example endorsement file above,
    // and publishing that to Rekor (https://rekor.sigstore.dev), as described
    // in https://github.com/sigstore/rekor/blob/main/types.md#pkixx509.
    // The resulting entry in Rekor has UUID
    // `bb05be1bd813f8afb7b77b2d9f7be5ae25b396d111c7a26a04b785c48c277372` and logIndex 1323526.
    // The body of LogEntry can be fetched using `rekor-cli get --log-index 1323526`.
    let log_entry_path = "../testdata/logentry.json";

    // Test public key, representing the product team that signed the endorsement file.
    let pubkey_path = "../testdata/ec_public.pem";

    // Public key of the Rekor instance hosted by sigstore.dev. It is downloaded from https://rekor.sigstore.dev/api/v1/log/publicKey.
    let rekor_pubkey_path = "../testdata/rekor_public_key.pem";

    let endorsement_bytes = fs::read(endorsement_path).expect("Couldn't read endorsement file.");
    let log_entry_bytes = fs::read(log_entry_path).expect("Couldn't read log entry file.");
    let rekor_pem_bytes =
        fs::read(rekor_pubkey_path).expect("Couldn't read Rekor's public key file.");
    let pubkey_pem_bytes =
        fs::read(pubkey_path).expect("Couldn't read product team's public key file.");

    let result = verify_rekor_log_entry(
        &log_entry_bytes,
        &rekor_pem_bytes,
        &pubkey_pem_bytes,
        &endorsement_bytes,
    );
    assert!(result.is_ok(), "{:?}", result);
}

#[test]
fn test_unmarshal_pem_public_key() {
    let pubkey_path = "../testdata/rekor_public_key.pem";
    let pem_bytes = fs::read(pubkey_path).expect("Couldn't read Rekor's public key file.");

    let key = unmarshal_pem_to_p256_public_key(&pem_bytes);
    assert!(key.is_ok());
}

#[test]
fn test_verify_rekor_signature() {
    let entry_path = "../testdata/logentry.json";
    let pubkey_path = "../testdata/rekor_public_key.pem";

    let log_entry_bytes = fs::read(entry_path).expect("Couldn't read Rekor log entry.");
    let pem_bytes = fs::read(pubkey_path).expect("Couldn't read Rekor's public key file.");

    let result = verify_rekor_signature(&log_entry_bytes, &pem_bytes);

    assert!(result.is_ok());
}
