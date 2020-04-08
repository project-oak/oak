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

use super::*;

#[test]
fn serialize_deserialize() {
    let labels = vec![
        Label {
            secrecy_tags: vec![],
            integrity_tags: vec![],
        },
        Label {
            secrecy_tags: vec![authorization_bearer_token_hmac_tag(&[0, 0, 0])],
            integrity_tags: vec![authorization_bearer_token_hmac_tag(&[1, 1, 1])],
        },
        Label {
            secrecy_tags: vec![
                authorization_bearer_token_hmac_tag(&[0, 0, 0]),
                authorization_bearer_token_hmac_tag(&[0, 0, 0]),
            ],
            integrity_tags: vec![
                authorization_bearer_token_hmac_tag(&[1, 1, 1]),
                authorization_bearer_token_hmac_tag(&[1, 1, 1]),
            ],
        },
        Label {
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
        let deserialized = Label::deserialize(&bytes).unwrap();
        assert_eq!(*label, deserialized);
    }
}

#[test]
fn label_flow() {
    let tag_0 = authorization_bearer_token_hmac_tag(&[0, 0, 0]);
    let tag_1 = authorization_bearer_token_hmac_tag(&[1, 1, 1]);

    let public_trusted = Label::public_trusted();

    // A label that corresponds to the secrecy of tag_0.
    //
    // A Node or channel with this label may have observed data related to tag_0.
    let label_0 = Label {
        secrecy_tags: vec![tag_0.clone()],
        integrity_tags: vec![],
    };

    // A label that corresponds to the secrecy of tag_1.
    //
    // A Node or channel with this label may have observed data related to tag_1.
    let label_1 = Label {
        secrecy_tags: vec![tag_1.clone()],
        integrity_tags: vec![],
    };

    // A label that corresponds to the combined secrecy of both tag_0 and tag_1.
    //
    // A Node or channel with this label may have observed data related to tag_0 and tag_1.
    let label_0_1 = Label {
        secrecy_tags: vec![tag_0.clone(), tag_1.clone()],
        integrity_tags: vec![],
    };

    // A label identical to `label_0_1`, but in which tags appear in a different order. This
    // should not make any difference in terms of what the label actually represent.
    let label_1_0 = Label {
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
