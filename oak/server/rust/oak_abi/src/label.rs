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

/// A trait representing a label as part of a lattice.
///
/// See https://github.com/project-oak/oak/blob/master/docs/concepts.md#labels
pub trait Label: Sized {
    /// Convert the label to bytes.
    fn serialize(&self) -> Vec<u8>;

    /// Build the label from bytes.
    fn deserialize(bytes: &[u8]) -> Option<Self>;

    /// Compare two labels according to the lattice structure: L_0 ⊑ L_1.
    fn flows_to(&self, other: &Self) -> bool;
}

impl Label for crate::proto::policy::Label {
    fn serialize(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        self.encode(&mut bytes)
            .expect("could not serialize to bytes");
        bytes
    }
    fn deserialize(bytes: &[u8]) -> Option<Self> {
        Self::decode(bytes).ok()
    }

    fn flows_to(&self, other: &Self) -> bool {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn authorization_bearer_token_hmac_tag(
        authorization_bearer_token_hmac: &[u8],
    ) -> crate::proto::policy::Tag {
        crate::proto::policy::Tag {
            tag: Option::Some(crate::proto::policy::tag::Tag::GrpcTag(
                crate::proto::policy::GrpcTag {
                    authorization_bearer_token_hmac: authorization_bearer_token_hmac.into(),
                },
            )),
        }
    }

    #[test]
    fn serialize_deserialize() {
        let labels = vec![
            crate::proto::policy::Label {
                secrecy_tags: vec![],
                integrity_tags: vec![],
            },
            crate::proto::policy::Label {
                secrecy_tags: vec![authorization_bearer_token_hmac_tag(&[0, 0, 0])],
                integrity_tags: vec![authorization_bearer_token_hmac_tag(&[1, 1, 1])],
            },
            crate::proto::policy::Label {
                secrecy_tags: vec![
                    authorization_bearer_token_hmac_tag(&[0, 0, 0]),
                    authorization_bearer_token_hmac_tag(&[0, 0, 0]),
                ],
                integrity_tags: vec![
                    authorization_bearer_token_hmac_tag(&[1, 1, 1]),
                    authorization_bearer_token_hmac_tag(&[1, 1, 1]),
                ],
            },
            crate::proto::policy::Label {
                secrecy_tags: vec![
                    authorization_bearer_token_hmac_tag(&[0, 0, 0]),
                    authorization_bearer_token_hmac_tag(&[1, 1, 1]),
                ],
                integrity_tags: vec![
                    authorization_bearer_token_hmac_tag(&[2, 2, 2]),
                    authorization_bearer_token_hmac_tag(&[3, 3, 3]),
                ],
            },
        ];
        for label in labels.iter() {
            let bytes = label.serialize();
            let deserialized = crate::proto::policy::Label::deserialize(&bytes).unwrap();
            assert_eq!(*label, deserialized);
        }
    }

    #[test]
    fn label_flow() {
        let tag_0 = authorization_bearer_token_hmac_tag(&[0, 0, 0]);
        let tag_1 = authorization_bearer_token_hmac_tag(&[1, 1, 1]);

        // The least privileged label.
        //
        // A node or channel with this label has only observed public data.
        let public_trusted = crate::proto::policy::Label {
            secrecy_tags: vec![],
            integrity_tags: vec![],
        };

        // A label that corresponds to the secrecy of tag_0.
        //
        // A node or channel with this label may have observed data related to tag_0.
        let label_0 = crate::proto::policy::Label {
            secrecy_tags: vec![tag_0.clone()],
            integrity_tags: vec![],
        };

        // A label that corresponds to the secrecy of tag_1.
        //
        // A node or channel with this label may have observed data related to tag_1.
        let label_1 = crate::proto::policy::Label {
            secrecy_tags: vec![tag_1.clone()],
            integrity_tags: vec![],
        };

        // A label that corresponds to the combined secrecy of both tag_0 and tag_1.
        //
        // A node or channel with this label may have observed data related to tag_0 and tag_1.
        let label_0_1 = crate::proto::policy::Label {
            secrecy_tags: vec![tag_0.clone(), tag_1.clone()],
            integrity_tags: vec![],
        };

        // A label identical to `label_0_1`, but in which tags appear in a different order. This
        // should not make any difference in terms of what the label actually represent.
        let label_1_0 = crate::proto::policy::Label {
            secrecy_tags: vec![tag_1, tag_0],
            integrity_tags: vec![],
        };

        // These labels form a lattice with the following shape:
        //
        //     (label_0_1 == label_1_0)
        //              /  \
        //             /    \
        //       label_0    label_1
        //             \     /
        //              \   /
        //          public_trusted

        // Data with any label can flow to the same label.
        assert_eq!(true, public_trusted.flows_to(&public_trusted));
        assert_eq!(true, label_0.flows_to(&label_0));
        assert_eq!(true, label_1.flows_to(&label_1));
        assert_eq!(true, label_0_1.flows_to(&label_0_1));
        assert_eq!(true, label_1_0.flows_to(&label_1_0));

        // label_0_1 and label_1_0 are effectively the same label, since the order of tags does not
        // matter.
        assert_eq!(true, label_0_1.flows_to(&label_1_0));
        assert_eq!(true, label_1_0.flows_to(&label_0_1));

        // public_trusted data can flow to more private data;
        assert_eq!(true, public_trusted.flows_to(&label_0));
        assert_eq!(true, public_trusted.flows_to(&label_1));
        assert_eq!(true, public_trusted.flows_to(&label_0_1));

        // Private data cannot flow to public_trusted.
        assert_eq!(false, label_0.flows_to(&public_trusted));
        assert_eq!(false, label_1.flows_to(&public_trusted));
        assert_eq!(false, label_0_1.flows_to(&public_trusted));

        // Private data with non-comparable labels cannot flow to each other.
        assert_eq!(false, label_0.flows_to(&label_1));
        assert_eq!(false, label_1.flows_to(&label_0));

        // Private data can flow to even more private data.
        assert_eq!(true, label_0.flows_to(&label_0_1));
        assert_eq!(true, label_1.flows_to(&label_0_1));

        // And vice versa.
        assert_eq!(false, label_0_1.flows_to(&label_0));
        assert_eq!(false, label_0_1.flows_to(&label_1));
    }
}
