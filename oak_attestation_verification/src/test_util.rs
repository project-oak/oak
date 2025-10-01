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

use intoto::statement::{
    make_statement, serialize_statement, DefaultPredicate, DefaultStatement, Statement,
};
use oak_proto_rust::oak::{
    attestation::v1::{
        binary_reference_value, kernel_binary_reference_value, verifying_key_reference_value,
        BinaryReferenceValue, ClaimReferenceValue, EndorsementReferenceValue,
        KernelBinaryReferenceValue, KeyType, SkipVerification, VerifyingKey,
        VerifyingKeyReferenceValue, VerifyingKeySet,
    },
    HexDigest,
};
use oak_time::{make_instant, Instant};
use p256::{ecdsa::signature::Signer, pkcs8::EncodePublicKey, NistP256, PublicKey};

/// A simple fake endorsement for basic generic testing purposes.
pub fn fake_endorsement(digest: &HexDigest, claim_types: Vec<&str>) -> DefaultStatement {
    make_statement(
        "fake_subject_name",
        digest,
        make_instant!("2025-10-01T12:08:00Z"),
        make_instant!("2025-09-01T12:00:00Z"),
        make_instant!("2025-12-01T12:00:00Z"),
        claim_types,
    )
}

/// Serialize the provided endorsement, sign it, and return both.
pub fn serialize_and_sign_endorsement(
    endorsement: &DefaultStatement,
    signing_key: ecdsa::SigningKey<NistP256>,
) -> (Vec<u8>, ecdsa::der::Signature<NistP256>) {
    let serialized_endorsement =
        serialize_statement(endorsement).expect("couldn't serialize endorsement");

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

/// Creates a [`BinaryReferenceValue`] with the provided endorser public key.
pub fn binary_reference_value_for_endorser_pk(public_key: PublicKey) -> BinaryReferenceValue {
    BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Endorsement(endorsement_reference_value(
            public_key,
        ))),
    }
}

/// Creates a [`KernelBinaryReferenceValue`] with the provided endorser public
/// key.
pub fn kernel_binary_reference_value_for_endorser_pk(
    public_key: PublicKey,
) -> KernelBinaryReferenceValue {
    KernelBinaryReferenceValue {
        r#type: Some(kernel_binary_reference_value::Type::Endorsement(
            endorsement_reference_value(public_key),
        )),
    }
}

fn endorsement_reference_value(public_key: PublicKey) -> EndorsementReferenceValue {
    let endorser_public_key =
        public_key.to_public_key_der().expect("Couldn't convert public key to DER").into_vec();
    let endorser_key = VerifyingKey {
        r#type: KeyType::EcdsaP256Sha256.into(),
        // Can use any valid Key ID, it remains unused with legacy attestation
        // verification.
        key_id: 1,
        raw: endorser_public_key.clone(),
    };
    EndorsementReferenceValue {
        endorser: Some(VerifyingKeySet { keys: [endorser_key].to_vec(), ..Default::default() }),
        required_claims: Some(ClaimReferenceValue { claim_types: vec![] }),
        rekor: Some(VerifyingKeyReferenceValue {
            r#type: Some(verifying_key_reference_value::Type::Skip(SkipVerification {})),
        }),
        ..Default::default()
    }
}

pub trait GetValidity {
    fn validity(&self) -> &intoto::statement::Validity;
}

impl GetValidity for Statement<DefaultPredicate> {
    fn validity(&self) -> &intoto::statement::Validity {
        self.predicate.validity.as_ref().expect("missing validity")
    }
}
