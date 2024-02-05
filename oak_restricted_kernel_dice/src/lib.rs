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

//! This crate contains the logic used by oak_restricted_kernel to create attestations. It is broken
//! out into a separate crate to allow this logic to be used independently used in tests to create
//! mock attestations, without also pulling in oak_restricted_kernel's allocator, which breaks
//! tests.

#![no_std]

extern crate alloc;

use coset::{cbor::Value, cwt::ClaimName, CborSerializable};
use hkdf::Hkdf;
use oak_crypto::hpke::Serializable;
use oak_dice::cert::{ENCLAVE_APPLICATION_LAYER_ID, LAYER_2_CODE_MEASUREMENT_ID, SHA2_256_ID};
use sha2::{Digest, Sha256};

/// A derived sealing key.
pub type DerivedKey = [u8; 32];

// Digest of an application.
pub type AppDigest = [u8; 32];

pub fn attest_application(
    stage0_dice_data: oak_dice::evidence::Stage0DiceData,
    app_bytes: &[u8],
) -> (DerivedKey, oak_dice::evidence::RestrictedKernelDiceData) {
    let app_digest = measure_app_digest(app_bytes);
    (
        generate_derived_key(&stage0_dice_data, &app_digest),
        generate_dice_data(stage0_dice_data, &app_digest),
    )
}

fn measure_app_digest(app_bytes: &[u8]) -> AppDigest {
    Sha256::digest(&app_bytes[..]).into()
}

fn generate_derived_key(
    stage0_dice_data: &oak_dice::evidence::Stage0DiceData,
    app_digest: &AppDigest,
) -> DerivedKey {
    // Mix in the application digest when deriving CDI for Layer 2.
    let hkdf = Hkdf::<Sha256>::new(Some(app_digest), &stage0_dice_data.layer_1_cdi.cdi[..]);
    let mut derived_key = DerivedKey::default();
    hkdf.expand(b"CDI_Seal", &mut derived_key)
        .expect("invalid length for derived key");
    derived_key
}

fn certificate_to_byte_array(cert: coset::CoseSign1) -> [u8; oak_dice::evidence::CERTIFICATE_SIZE] {
    let vec = cert.to_vec().expect("couldn't serialize certificate");
    let mut slice = [0; oak_dice::evidence::CERTIFICATE_SIZE];
    slice[..vec.len()].copy_from_slice(&vec);
    slice
}

/// Generates attestation evidence for the 'measurement' of the application.
pub fn generate_dice_data(
    stage0_dice_data: oak_dice::evidence::Stage0DiceData,
    app_digest: &AppDigest,
) -> oak_dice::evidence::RestrictedKernelDiceData {
    let (application_keys, application_private_keys): (
        oak_dice::evidence::ApplicationKeys,
        oak_dice::evidence::ApplicationPrivateKeys,
    ) = {
        let kernel_signing_key = p256::ecdsa::SigningKey::from_slice(
            &stage0_dice_data
                .layer_1_certificate_authority
                .eca_private_key[..oak_dice::evidence::P256_PRIVATE_KEY_SIZE],
        )
        .expect("failed to parse the layer1 ECDSA private key bytes");

        let kernel_cert_issuer = stage0_dice_data
            .layer_1_evidence
            .claims()
            .expect("failed to get stage0 claims")
            // The kernel was the subject of layer 1.
            .subject
            .expect("expected to find the subject");

        let (application_private_signing_key, application_public_verifying_key) =
            oak_dice::cert::generate_ecdsa_key_pair();

        let additional_claims = alloc::vec![(
            ClaimName::PrivateUse(ENCLAVE_APPLICATION_LAYER_ID),
            Value::Map(alloc::vec![(
                Value::Integer(LAYER_2_CODE_MEASUREMENT_ID.into()),
                Value::Map(alloc::vec![(
                    Value::Integer(SHA2_256_ID.into()),
                    Value::Bytes(app_digest.into()),
                )]),
            ),]),
        )];

        let application_signing_public_key_certificate =
            oak_dice::cert::generate_signing_certificate(
                &kernel_signing_key,
                kernel_cert_issuer.clone(),
                &application_public_verifying_key,
                additional_claims.clone(),
            )
            .expect("couldn't generate signing certificate");

        let (application_encryption_private_key, application_encryption_public_key) =
            oak_crypto::hpke::gen_kem_keypair();

        let application_encryption_public_key_certificate =
            oak_dice::cert::generate_kem_certificate(
                &kernel_signing_key,
                kernel_cert_issuer,
                application_encryption_public_key.to_bytes().as_slice(),
                additional_claims,
            )
            .expect("couldn't generate encryption public certificate");

        let application_keys = oak_dice::evidence::ApplicationKeys {
            signing_public_key_certificate: certificate_to_byte_array(
                application_signing_public_key_certificate,
            ),
            encryption_public_key_certificate: certificate_to_byte_array(
                application_encryption_public_key_certificate,
            ),
        };

        let application_private_keys = {
            let signing_private_key = {
                let bytes = application_private_signing_key.to_bytes();
                let mut slice = [0; oak_dice::evidence::PRIVATE_KEY_SIZE];
                slice[..bytes.as_slice().len()].copy_from_slice(bytes.as_slice());
                slice
            };

            let encryption_private_key = {
                let mut slice = [0; oak_dice::evidence::PRIVATE_KEY_SIZE];
                slice[..application_encryption_private_key.to_bytes().len()]
                    .copy_from_slice(&application_encryption_private_key.to_bytes());
                slice
            };

            oak_dice::evidence::ApplicationPrivateKeys {
                encryption_private_key,
                signing_private_key,
            }
        };

        (application_keys, application_private_keys)
    };

    let evidence = oak_dice::evidence::Evidence {
        root_layer_evidence: stage0_dice_data.root_layer_evidence,
        restricted_kernel_evidence: stage0_dice_data.layer_1_evidence,
        application_keys,
    };

    oak_dice::evidence::RestrictedKernelDiceData {
        evidence,
        application_private_keys,
    }
}
