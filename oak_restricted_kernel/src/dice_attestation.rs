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
use zerocopy::FromZeroes;

/// Generates an ECA certificate for use by the application.
fn generate_application_certificate(
    kernel_eca_key: &p256::ecdsa::SigningKey,
    kernel_cert_issuer: alloc::string::String,
    app_digest: &[u8],
) -> (coset::CoseSign1, p256::ecdsa::SigningKey) {
    // Generate additional claims to cover the measurements.

    let additional_claims = alloc::vec![(
        coset::cwt::ClaimName::PrivateUse(oak_dice::cert::CODE_DIGEST_ID),
        coset::cbor::value::Value::Bytes(app_digest.into()),
    )];
    oak_dice::cert::generate_eca_certificate(kernel_eca_key, kernel_cert_issuer, additional_claims)
        .expect("couldn't generate ECA certificate")
}

/// Generates attestation evidence for the 'measurement' of the application.
pub fn generate_dice_data(
    stage0_dice_data: oak_dice::evidence::Stage0DiceData,
    app_digest: &[u8],
) -> oak_dice::evidence::RestrictedKernelDiceData {
    // Generate ECA Stage0 key pair. This key will be used to sign Stage1 ECA certificate.
    let (kernel_eca_key, kernel_eca_verifying_key) = oak_dice::cert::generate_ecdsa_key_pair();

    let (application_signing_public_key_certificate, application_signing_private_key) =
        generate_application_certificate(
            &kernel_eca_key,
            hex::encode(oak_dice::cert::derive_public_key_id(
                &kernel_eca_verifying_key,
            )),
            app_digest,
        );

    let application_keys = {
        let mut keys = oak_dice::evidence::ApplicationKeys::new_zeroed();
        let signing_public_key_certificate_vec = application_signing_public_key_certificate
            .to_vec()
            .expect("couldn't serialize application signing 1 ECA certificate");
        keys.signing_public_key_certificate[..signing_public_key_certificate_vec.len()]
            .copy_from_slice(&signing_public_key_certificate_vec);
        keys
    };

    let application_private_keys: oak_dice::evidence::ApplicationPrivateKeys = {
        let signing_private_key_bytes = application_signing_private_key.to_bytes();
        let mut keys = oak_dice::evidence::ApplicationPrivateKeys::new_zeroed();
        keys.signing_private_key[..signing_private_key_bytes.as_slice().len()]
            .copy_from_slice(signing_private_key_bytes.as_slice());
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
