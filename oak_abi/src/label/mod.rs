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

//! Labels represent the kinds of information that is allowed to be processed
//! by entities in the Oak system. The Oak Runtime allows Oak Nodes to manipulate
//! labels, and so the labels need to be passed across the Oak ABI in a defined
//! binary format.  That format is a serialized protocol buffer holding the
//! `Label` message defined in the policy.proto file.

use prost::Message;
use std::collections::HashSet;

pub use crate::proto::oak::label::*;

#[cfg(test)]
mod tests;

/// Add helper methods to the `Label` struct that is auto-generated from
/// the protobuf message definition.
impl crate::proto::oak::label::Label {
    /// Convert a label to bytes.
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

    /// Return the least privileged label.
    ///
    /// A Node or channel with this label has only observed public data and is trusted by no one.
    pub fn public_untrusted() -> Self {
        Label {
            confidentiality_tags: vec![],
            integrity_tags: vec![],
        }
    }

    /// Compare two labels according to the lattice structure: L_0 ⊑ L_1.
    pub fn flows_to(&self, other: &Self) -> bool {
        #![allow(clippy::mutable_key_type)]

        let self_confidentiality_tags: HashSet<_> = self.confidentiality_tags.iter().collect();
        let other_confidentiality_tags: HashSet<_> = other.confidentiality_tags.iter().collect();
        let self_integrity_tags: HashSet<_> = self.integrity_tags.iter().collect();
        let other_integrity_tags: HashSet<_> = other.integrity_tags.iter().collect();

        // The target label must have (compared to the self label):
        // - same or more confidentiality tags
        // - same or fewer integrity tags
        self_confidentiality_tags.is_subset(&other_confidentiality_tags)
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
