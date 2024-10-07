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

use alloc::collections::btree_map::BTreeMap;

use oak_proto_rust::oak::{
    attestation::v1::{binary_reference_value, BinaryReferenceValue, EndorsementReferenceValue},
    RawDigest,
};
use p256::{ecdsa::signature::Signer, pkcs8::EncodePublicKey, NistP256, PublicKey};
use time::macros::datetime;

use crate::endorsement::{
    self, DefaultPredicate, DefaultStatement, Subject, Validity as EndorsementValidity,
};

pub enum Usage {
    None,
    Firmware,
}

impl Usage {
    fn to_string(&self) -> String {
        match self {
            Self::None => "".to_string(),
            Self::Firmware => "firmware".to_string(),
        }
    }
}
/// A simple fake endorsement for basic generic testing purposes.
pub fn fake_endorsement(digests: &RawDigest, usage: Usage) -> DefaultStatement {
    let map_digests = raw_digest_to_map(digests);

    DefaultStatement {
        _type: endorsement::STATEMENT_TYPE.to_owned(),
        predicate_type: endorsement::PREDICATE_TYPE_V3.to_owned(),
        subject: vec![Subject { name: "Fake Subject".to_string(), digest: map_digests }],
        predicate: DefaultPredicate {
            usage: usage.to_string(),
            issued_on: datetime!(2024-10-01 12:08 UTC),
            validity: Some(EndorsementValidity {
                not_before: datetime!(2024-09-01 12:00 UTC),
                not_after: datetime!(2024-12-01 12:00 UTC),
            }),
            claims: vec![],
        },
    }
}

/// Serialize the provided endorsement, sign it, and return both.
pub fn serialize_and_sign_endorsement(
    endorsement: &DefaultStatement,
    signing_key: ecdsa::SigningKey<NistP256>,
) -> (Vec<u8>, ecdsa::der::Signature<NistP256>) {
    let serialized_endorsement =
        serde_json::to_vec(&endorsement).expect("couldn't serialize test endorsement");

    let endorsement_signature: ecdsa::Signature<p256::NistP256> =
        signing_key.sign(&serialized_endorsement);

    (serialized_endorsement, endorsement_signature.to_der())
}

/// Create a new random keypair suitable for signing an endorsement in the way
/// that the Oak attestation framework expects.
pub fn new_random_signing_keypair() -> (p256::ecdsa::SigningKey, p256::PublicKey) {
    use rand_core::OsRng;
    let secret_key = p256::SecretKey::random(&mut OsRng);
    let public_key = secret_key.public_key();
    (secret_key.into(), public_key)
}

/// Creates a [`BinaryReferenceValue`]` with the provided `public_key`, and all
/// other fields unset.
pub fn binary_reference_value_for_endorser_pk(public_key: PublicKey) -> BinaryReferenceValue {
    BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Endorsement(EndorsementReferenceValue {
            endorser_public_key: public_key
                .to_public_key_der()
                .expect("Couldn't convert public key to DER")
                .into_vec(),
            ..Default::default()
        })),
    }
}

fn raw_digest_to_map(h: &RawDigest) -> BTreeMap<String, String> {
    let mut map = BTreeMap::<String, String>::new();

    macro_rules! insert_if_present {
        ($field:ident) => {
            if !h.$field.is_empty() {
                map.insert(stringify!($field).into(), hex::encode(&h.$field));
            }
        };
    }

    insert_if_present!(psha2);
    insert_if_present!(sha1);
    insert_if_present!(sha2_256);
    insert_if_present!(sha2_512);
    insert_if_present!(sha3_512);
    insert_if_present!(sha3_384);
    insert_if_present!(sha3_256);
    insert_if_present!(sha3_224);
    insert_if_present!(sha2_384);

    map
}
