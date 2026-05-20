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
    DefaultPredicate, DefaultStatement, Statement, make_statement, serialize_statement,
};
use oak_digest::{hex_digest_from_contents, raw_to_hex_digest};
use oak_proto_rust::oak::{
    HexDigest, RawDigest,
    attestation::v1::{
        BinaryReferenceValue, Endorsement, EndorsementReferenceValue, KernelBinaryReferenceValue,
        Signature, SignedEndorsement, binary_reference_value, endorsement::Format,
        kernel_binary_reference_value,
    },
};
use oak_time::{Instant, make_instant};
use p256::{NistP256, PublicKey, ecdsa::signature::Signer, pkcs8::EncodePublicKey};
use verify_endorsement::{
    create_endorsement_reference_value, create_tlog_reference_values_skip,
    create_verifying_key_from_raw,
};

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

pub fn endorsement_reference_value(public_key: PublicKey) -> EndorsementReferenceValue {
    let endorser_public_key =
        public_key.to_public_key_der().expect("Couldn't convert public key to DER").into_vec();
    let endorser_key = create_verifying_key_from_raw(&endorser_public_key, 1);
    create_endorsement_reference_value(
        endorser_key,
        Vec::new(),
        create_tlog_reference_values_skip(),
    )
}

/// Creates a [`SignedEndorsement`] from a pre-built in-toto statement.
pub fn sign_endorsement(
    statement: &DefaultStatement,
    signing_key: &p256::ecdsa::SigningKey,
    subject: &[u8],
) -> SignedEndorsement {
    let (serialized, signature) = serialize_and_sign_endorsement(statement, signing_key.clone());
    SignedEndorsement {
        endorsement: Some(Endorsement {
            format: Format::EndorsementFormatJsonIntoto.into(),
            serialized,
            subject: subject.to_vec(),
        }),
        signature: Some(Signature { key_id: 1, raw: signature.as_bytes().to_vec() }),
        ..Default::default()
    }
}

/// Creates a [`SignedEndorsement`] where the in-toto statement's subject
/// digest is the sha2_256 measurement itself (not a hash of it).
///
/// Use this for cases where `acquire_expected_digests` is called — it
/// extracts the `HexDigest` from the statement and converts it to a
/// `RawDigest` to compare against the evidence measurement directly.
pub fn make_signed_endorsement_for_digest(
    measurement: &[u8],
    not_before: Instant,
    not_after: Instant,
    signing_key: &p256::ecdsa::SigningKey,
    claim_types: Vec<&str>,
) -> SignedEndorsement {
    let hex_digest =
        raw_to_hex_digest(&RawDigest { sha2_256: measurement.to_vec(), ..Default::default() });
    let statement = make_statement(
        "fake_subject_name",
        &hex_digest,
        not_before,
        not_before,
        not_after,
        claim_types,
    );
    sign_endorsement(&statement, signing_key, measurement)
}

/// Creates a [`SignedEndorsement`] for serialized contents (e.g.
/// `KernelAttachment` or `MpmAttachment`). The in-toto statement's
/// subject digest is the SHA-256 of `contents`.
pub fn make_signed_endorsement_for_contents(
    contents: &[u8],
    not_before: Instant,
    not_after: Instant,
    signing_key: &p256::ecdsa::SigningKey,
    claim_types: Vec<&str>,
) -> SignedEndorsement {
    let hex_digest = hex_digest_from_contents(contents);
    let statement = make_statement(
        "fake_subject_name",
        &hex_digest,
        not_before,
        not_before,
        not_after,
        claim_types,
    );
    sign_endorsement(&statement, signing_key, contents)
}

pub trait GetValidity {
    fn validity(&self) -> &intoto::statement::Validity;
}

impl GetValidity for Statement<DefaultPredicate> {
    fn validity(&self) -> &intoto::statement::Validity {
        self.predicate.validity.as_ref().expect("missing validity")
    }
}
