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
//! Representations and management of Roughtime's online and long-term Ed25519 keys
//!

mod longterm;
mod online;

use std::fmt::Display;
use std::fmt::Formatter;
use std::str::FromStr;

pub use self::longterm::LongTermKey;
pub use self::online::OnlineKey;

/// Methods for protecting the server's long-term identity
#[derive(Debug, PartialEq, Eq, PartialOrd, Hash, Clone)]
pub enum KmsProtection {
    /// No protection, seed is in plaintext
    Plaintext,

    /// Envelope encryption of the seed using AWS Key Management Service
    AwsKmsEnvelope(String),

    /// Envelope encryption of the seed using Google Cloud Key Management Service
    GoogleKmsEnvelope(String),
}

impl Display for KmsProtection {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        match self {
            KmsProtection::Plaintext => write!(f, "Plaintext"),
            KmsProtection::AwsKmsEnvelope(key_id) => write!(f, "AwsKms({})", key_id),
            KmsProtection::GoogleKmsEnvelope(key_id) => write!(f, "GoogleKms({})", key_id),
        }
    }
}

impl FromStr for KmsProtection {
    type Err = String;

    fn from_str(s: &str) -> Result<KmsProtection, String> {
        match s {
            "plaintext" => Ok(KmsProtection::Plaintext),
            s if s.starts_with("arn:") => Ok(KmsProtection::AwsKmsEnvelope(s.to_string())),
            s if s.starts_with("projects/") => Ok(KmsProtection::GoogleKmsEnvelope(s.to_string())),
            s => Err(format!("unknown KmsProtection '{}'", s)),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::key::KmsProtection;
    use std::str::FromStr;

    #[test]
    fn convert_from_string() {
        let arn =
            "arn:aws:kms:some-aws-region:111122223333:key/1234abcd-12ab-34cd-56ef-1234567890ab";
        let resource_id =
            "projects/key-project/locations/global/keyRings/key-ring/cryptoKeys/my-key";

        match KmsProtection::from_str("plaintext") {
            Ok(KmsProtection::Plaintext) => (),
            e => panic!("unexpected result {:?}", e),
        };
        match KmsProtection::from_str(arn) {
            Ok(KmsProtection::AwsKmsEnvelope(msg)) => assert_eq!(msg, arn),
            e => panic!("unexpected result {:?}", e),
        }
        match KmsProtection::from_str(resource_id) {
            Ok(KmsProtection::GoogleKmsEnvelope(msg)) => assert_eq!(msg, resource_id),
            e => panic!("unexpected result {:?}", e),
        }
        match KmsProtection::from_str("frobble") {
            Err(msg) => assert!(msg.contains("unknown KmsProtection")),
            e => panic!("unexpected result {:?}", e),
        }
    }
}
