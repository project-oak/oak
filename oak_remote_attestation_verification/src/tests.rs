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
    // Example endorsement file generated with the following provenance as the evidence:
    // https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha256:b28696a8341443e3ba433373c60fe1eba8d96f28c8aff6c5ee03d752dd3b399b
    let endorsement_path = "testdata/endorsement.json";

    // LogEntry downloaded from
    // https://rekor.sigstore.dev/api/v1/log/entries/24296fb24b8ad77a51d549703a3a1c2dd2639ba49617fc563854031cb93e6d354e7b005065c334a8.
    // This LogEntry was created by signing the example endorsement file above, using google-cloud
    // KMS, and uploading it to Rekor (https://rekor.sigstore.dev) using `rekor-cli`, as described
    // in https://github.com/sigstore/rekor/blob/main/types.md#pkixx509.
    // The resulting entry in Rekor has UUID
    // `24296fb24b8ad77a51d549703a3a1c2dd2639ba49617fc563854031cb93e6d354e7b005065c334a8` and
    // logIndex 30891523. The body of LogEntry can be fetched using `rekor-cli get --log-index
    // 30891523`.
    let log_entry_path = "testdata/logentry.json";

    // Public key fetched from Google Cloud KMS, associated with the signing key that was used for
    // signing the endorsement statement.
    let pubkey_path = "testdata/oak-development.pem";

    // Public key of the Rekor instance hosted by sigstore.dev. It is downloaded from
    // https://rekor.sigstore.dev/api/v1/log/publicKey.
    let rekor_pubkey_path = "testdata/rekor_public_key.pem";

    let endorsement_bytes = fs::read(endorsement_path).expect("couldn't read endorsement file");
    let log_entry_bytes = fs::read(log_entry_path).expect("couldn't read log entry file");
    let rekor_pem_bytes =
        fs::read(rekor_pubkey_path).expect("couldn't read Rekor's public key file");
    let pubkey_pem_bytes =
        fs::read(pubkey_path).expect("couldn't read product team's public key file");

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
    let pubkey_path = "testdata/rekor_public_key.pem";
    let pem_bytes = fs::read(pubkey_path).expect("couldn't read Rekor's public key file");

    let key = unmarshal_pem_to_p256_public_key(&pem_bytes);
    assert!(key.is_ok());
}

#[test]
fn test_verify_rekor_signature() {
    let entry_path = "testdata/logentry.json";
    let pubkey_path = "testdata/rekor_public_key.pem";

    let log_entry_bytes = fs::read(entry_path).expect("couldn't read Rekor log entry");
    let pem_bytes = fs::read(pubkey_path).expect("couldn't read Rekor's public key file");

    let result = verify_rekor_signature(&log_entry_bytes, &pem_bytes);

    assert!(result.is_ok());
}
