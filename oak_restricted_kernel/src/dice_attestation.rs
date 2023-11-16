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

use coset::CborSerializable;
use oak_dice::evidence::ApplicationKeys;
use zerocopy::FromZeroes;

fn certificate_to_owned_slice(
    cert: coset::sign::CoseSign1,
) -> [u8; oak_dice::evidence::CERTIFICATE_SIZE] {
    let vec = cert.to_vec().expect("couldn't serialize certificate");
    let slice = [u8; oak_dice::evidence::CERTIFICATE_SIZE];
    slice[..vec.len()].copy_from_slice(&vec);
    slice
}

fn private_key_to_owned_slice(
    key: SigningKey<NistP256>,
) -> [u8; oak_dice::evidence::PRIVATE_KEY_SIZE] {
    let bytes = key.to_bytes();
    let slice = [u8; oak_dice::evidence::PRIVATE_KEY_SIZE];
    slice[..bytes.as_slice().len()].copy_from_slice(bytes.as_slice());
    slice
}

/// Generates attestation evidence for the 'measurement' of the application.
pub fn generate_dice_data(
    stage0_dice_data: oak_dice::evidence::Stage0DiceData,
    app_digest: &[u8],
) -> oak_dice::evidence::RestrictedKernelDiceData {
    let (application_keys, application_private_keys): (
        oak_dice::evidence::ApplicationKeys,
        oak_dice::evidence::ApplicationPrivateKeys,
    ) = {
        let (application_private_signing_key, application_public_verifying_key) =
            oak_dice::cert::generate_ecdsa_key_pair();

        let kernel_cert_issuer = stage0_dice_data
            .layer_1_evidence
            .claims()
            .expect("failed to get stage0 claims")
            // The kernel was the subject of layer 1.
            .subject
            .expect("expected to find the subject");

        let additional_claims = alloc::vec![(
            coset::cwt::ClaimName::PrivateUse(oak_dice::cert::LAYER_2_CODE_MEASUREMENT_ID),
            coset::cbor::value::Value::Bytes(app_digest.into()),
        )];

        let application_signing_public_key_certificate =
            oak_dice::cert::generate_signing_certificate(
                &kernel_signing_key,
                kernel_cert_issuer.clone(),
                &application_public_verifying_key,
                additional_claims.clone(),
            )
            .expect("couldn't generate signing certificate");

        let (application_encryption_private_key, application_encryption_public_key) = {
            let application_encryption_key_provider =
                oak_crypto::encryptor::EncryptionKeyProvider::new();
            (
                application_encryption_key_provider.get_serialized_private_key(),
                application_encryption_key_provider.get_serialized_public_key(),
            )
        };

        let application_encryption_public_key_certificate =
            oak_dice::cert::generate_kem_certificate(
                &kernel_signing_key,
                kernel_cert_issuer,
                &application_encryption_public_key,
                additional_claims,
            )
            .expect("couldn't generate encryption public certificate");

        let application_keys = oak_dice::evidence::ApplicationKeys {
            signing_public_key_certificate: certificate_to_owned_slice(
                application_signing_public_key_certificate,
            ),
            encryption_public_key_certificate: certificate_to_owned_slice(
                application_encryption_public_key_certificate,
            ),
        };

        let application_private_keys = oak_dice::evidence::ApplicationPrivateKeys {
            signing_private_key: private_key_to_owned_slice(application_encryption_private_key),
            encryption_private_key: private_key_to_owned_slice(application_private_signing_key),
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
