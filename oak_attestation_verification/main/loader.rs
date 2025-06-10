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

use std::{fs, path::PathBuf};

use anyhow::Result;
use derive_builder::Builder;
use oak_proto_rust::oak::attestation::v1::{
    endorsement::Format, Endorsement, Signature, SignedEndorsement,
};

use crate::KEY_ID;

pub(crate) trait EndorsementLoader {
    fn load_endorsement(&self) -> Result<SignedEndorsement>;
}

#[derive(Builder)]
pub(crate) struct FileEndorsementLoader {
    endorsement_path: PathBuf,
    signature_path: PathBuf,
    log_entry_path: Option<PathBuf>,
    subject_path: Option<PathBuf>,
}

impl EndorsementLoader for FileEndorsementLoader {
    fn load_endorsement(&self) -> Result<SignedEndorsement> {
        let endorsement = fs::read(&self.endorsement_path).expect("couldn't read endorsement");
        let signature = fs::read(&self.signature_path).expect("couldn't read signature");
        let log_entry = match &self.log_entry_path {
            None => Vec::new(),
            Some(path) => fs::read(path).expect("couldn't read log entry"),
        };
        let subject = match &self.subject_path {
            None => Vec::new(),
            Some(path) => fs::read(path).expect("couldn't read subject"),
        };
        let signed_endorsement = SignedEndorsement {
            endorsement: Some(Endorsement {
                format: Format::EndorsementFormatJsonIntoto.into(),
                serialized: endorsement.to_vec(),
                subject: subject.clone(),
            }),
            signature: Some(Signature { key_id: KEY_ID, raw: signature.to_vec() }),
            rekor_log_entry: log_entry.clone(),
        };
        Ok(signed_endorsement)
    }
}
