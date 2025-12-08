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

use std::fmt;

use anyhow::Result;
use sha2::{Digest as Sha2Digest, Sha256};

/// A digest of some underlying data.
/// Currently only holds SHA2-256, but may be extended in the future.
#[derive(Debug, PartialEq, Eq)]
pub enum Digest {
    Sha256(Vec<u8>),
}

impl Digest {
    pub fn from_hex(s: &str) -> Result<Self> {
        let parts: Vec<&str> = s.split(':').collect();
        if parts.len() != 2 {
            anyhow::bail!("invalid digest format");
        }
        let algo = parts[0];
        let hex_digest = parts[1];
        match algo {
            "sha256" => {
                let digest = hex::decode(hex_digest)?;
                Ok(Digest::Sha256(digest))
            }
            _ => anyhow::bail!("unsupported algorithm: {algo}"),
        }
    }

    pub fn algo(&self) -> &str {
        match self {
            Digest::Sha256(_) => "sha256",
        }
    }

    pub fn to_hex(&self) -> String {
        match self {
            Digest::Sha256(digest) => hex::encode(digest),
        }
    }
}

impl fmt::Display for Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.algo(), self.to_hex())
    }
}

pub fn compute_canonical_digest(data: &[u8]) -> Digest {
    let mut hasher = Sha256::new();
    hasher.update(data);
    Digest::Sha256(hasher.finalize().to_vec())
}
