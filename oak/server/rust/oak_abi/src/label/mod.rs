//
// Copyright 2020 The Project Oak Authors
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

//! Labels are defined at the ABI level because they need to be available:
//!
//! - to applications (e.g. via the SDK), so that they can be manipulated by running Oak Nodes
//! - to the Runtime, so that they can be checked and enforced when data is exchanged between Nodes
//!   over Channels
//!
//! In order to support this, Labels are serialized and deserialized across the ABI boundary, and
//! can be read and write using ABI functions.

use prost::Message;

// We use `hashbrown` since it is `no_std` compatible.
use hashbrown::HashSet;

pub use crate::proto::label::*;

#[cfg(test)]
mod tests;

/// A proto message representing a label as part of a lattice.
impl crate::proto::label::Label {
    /// Convert the label to bytes.
    pub fn serialize(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        self.encode(&mut bytes)
            .expect("could not serialize to bytes");
        bytes
    }

    /// Build the label from bytes.
    pub fn deserialize(bytes: &[u8]) -> Option<Self> {
        Self::decode(bytes).ok()
    }

    // Return the least privileged label.
    //
    // A Node or channel with this label has only observed public data and is trusted by no one.
    pub fn public_trusted() -> Self {
        Label {
            secrecy_tags: vec![],
            integrity_tags: vec![],
        }
    }

    /// Compare two labels according to the lattice structure: L_0 ⊑ L_1.
    pub fn flows_to(&self, other: &Self) -> bool {
        #![allow(clippy::mutable_key_type)]

        let self_secrecy_tags: HashSet<_> = self.secrecy_tags.iter().collect();
        let other_secrecy_tags: HashSet<_> = other.secrecy_tags.iter().collect();
        let self_integrity_tags: HashSet<_> = self.integrity_tags.iter().collect();
        let other_integrity_tags: HashSet<_> = other.integrity_tags.iter().collect();

        // The target label must have (compared to the self label):
        // - same or more secrecy tags
        // - same or fewer integrity tags
        self_secrecy_tags.is_subset(&other_secrecy_tags)
            && other_integrity_tags.is_subset(&self_integrity_tags)
    }
}

/// Creates a [`Tag`] having as principal the provided authorization bearer token.
///
/// See https://github.com/project-oak/oak/blob/master/oak/proto/label.proto
pub fn authorization_bearer_token_hmac_tag(authorization_bearer_token_hmac: &[u8]) -> Tag {
    Tag {
        tag: Some(tag::Tag::GrpcTag(GrpcTag {
            authorization_bearer_token_hmac: authorization_bearer_token_hmac.into(),
        })),
    }
}
