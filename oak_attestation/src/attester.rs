//
// Copyright 2023 The Project Oak Authors
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

use alloc::vec::Vec;

use prost::Message;

use crate::proto::oak::{attestation::v1::Evidence, session::v1::AttestationEvidence};

impl From<Evidence> for AttestationEvidence {
    fn from(evidence: Evidence) -> Self {
        let (encryption_public_key, signing_public_key) = match &evidence.application_keys {
            Some(keys) => (
                keys.encryption_public_key_certificate.clone(),
                keys.signing_public_key_certificate.clone(),
            ),
            None => (Vec::new(), Vec::new()),
        };
        AttestationEvidence {
            attestation: evidence.encode_to_vec(),
            encryption_public_key,
            signing_public_key,
            signed_application_data: Vec::new(),
        }
    }
}
