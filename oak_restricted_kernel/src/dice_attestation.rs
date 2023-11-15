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

use crate::alloc::string::ToString;
use coset::CborSerializable;
use zerocopy::FromZeroes;

/// Generates an ECA certificate for use by the application.
fn generate_application_certificate(
    kernel_signing_key: &p256::ecdsa::SigningKey,
    kernel_cert_issuer: alloc::string::String,
    application_verifying_key: &p256::ecdsa::VerifyingKey,
    app_digest: &[u8],
) -> coset::CoseSign1 {
    let additional_claims = alloc::vec![(
        coset::cwt::ClaimName::PrivateUse(oak_dice::cert::LAYER_2_CODE_MEASUREMENT_ID),
        coset::cbor::value::Value::Bytes(app_digest.into()),
    )];
    oak_dice::cert::generate_signing_certificate(
        kernel_signing_key,
        kernel_cert_issuer,
        application_verifying_key,
        additional_claims,
    )
    .expect("couldn't generate signing certificate")
}

/// Generates attestation evidence for the 'measurement' of the application.
pub fn generate_dice_data(
    stage0_dice_data: oak_dice::evidence::Stage0DiceData,
    app_digest: &[u8],
) -> oak_dice::evidence::RestrictedKernelDiceData {
    let (application_signing_key, application_verifying_key) =
        oak_dice::cert::generate_ecdsa_key_pair();

    let application_eca_cert = {
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

        generate_application_certificate(
            &kernel_signing_key,
            kernel_cert_issuer,
            &application_verifying_key,
            app_digest,
        )
    };

    let application_keys = {
        let mut keys = oak_dice::evidence::ApplicationKeys::new_zeroed();
        let application_eca_cert_vec = application_eca_cert
            .to_vec()
            .expect("couldn't serialize application signing 1 ECA certificate");
        keys.signing_public_key_certificate[..application_eca_cert_vec.len()]
            .copy_from_slice(&application_eca_cert_vec);
        // TODO(#4074): Implement the encryption key.
        keys
    };

    let application_private_keys: oak_dice::evidence::ApplicationPrivateKeys = {
        let signing_private_key_bytes = application_signing_key.to_bytes();
        let mut keys = oak_dice::evidence::ApplicationPrivateKeys::new_zeroed();
        keys.signing_private_key[..signing_private_key_bytes.as_slice().len()]
            .copy_from_slice(signing_private_key_bytes.as_slice());
        // TODO(#4074): Implement the encryption key.
        keys
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
