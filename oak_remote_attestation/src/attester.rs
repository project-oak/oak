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

use crate::proto::oak::{
    attestation::v1::{ApplicationKeys, CertificateAuthority, DiceData, Evidence, LayerEvidence},
    session::v1::AttestationEvidence,
};
use alloc::{string::ToString, sync::Arc, vec, vec::Vec};
use anyhow::Context;
use oak_crypto::encryptor::EncryptionKeyProvider;
use oak_dice::cert::generate_ecdsa_key_pair;

/// A trait implementing the functionality of generating a remote attestation report.
///
/// An implementation of this trait is expected to run in a TEE (i.e. it is usually in the server).
pub trait AttestationReportGenerator: Send + Sync {
    /// Generate a remote attestation report, ensuring that `attested_data` is cryptographically
    /// bound to the result (e.g. via a signature).
    fn generate_attestation_report(&self, attested_data: &[u8]) -> anyhow::Result<Vec<u8>>;
}

/// An instance of [`AttestationReportGenerator`] that always returns an empty attestation.
///
/// Useful when no attestation is expected to be genereated by the current side of a remotely
/// attested connection.
#[derive(Clone)]
pub struct EmptyAttestationReportGenerator;

impl AttestationReportGenerator for EmptyAttestationReportGenerator {
    fn generate_attestation_report(&self, _attested_data: &[u8]) -> anyhow::Result<Vec<u8>> {
        Ok(Vec::new())
    }
}

/// A struct implementing the functionality of an attester that generates an attestation evidence.
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-attester>
pub struct Attester {
    attestation_report_generator: Arc<dyn AttestationReportGenerator>,
    encryption_key_provider: Arc<EncryptionKeyProvider>,
}

impl Attester {
    pub fn new(
        attestation_report_generator: Arc<dyn AttestationReportGenerator>,
        encryption_key_provider: Arc<EncryptionKeyProvider>,
    ) -> Self {
        Self {
            attestation_report_generator,
            encryption_key_provider,
        }
    }

    /// Generate an attestation evidence containing a remote attestation report and ensuring that
    /// `attested_data` is cryptographically bound to the result (e.g. via a signature).
    pub fn generate_attestation_evidence(&self) -> anyhow::Result<AttestationEvidence> {
        let encryption_public_key = self.encryption_key_provider.get_serialized_public_key();
        let attestation_report = self
            .attestation_report_generator
            .generate_attestation_report(&encryption_public_key)
            .context("couldn't generate attestation report")?;
        Ok(AttestationEvidence {
            attestation: attestation_report,
            encryption_public_key,
            // TODO(#3836): Implement signature generation and add the signing key.
            signing_public_key: Vec::new(),
            // TODO(#3640): Sign application data.
            signed_application_data: Vec::new(),
        })
    }
}

struct ApplicationPublicKeys {
    encryption_public_key: Option<Vec<u8>>,
    signing_public_key: Option<Vec<u8>>,
}

// TODO(#4074): Rename to `Attester` and replace the existing `Attester`once
// DICE attestation is implemented.
/// DICE attester implementation.
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-attester>
struct DiceAttester {
    /// DICE attestation evidence that includes current layer's evidence.
    evidence: Evidence,
    /// Certificate authority for the current layer.
    certificate_authority: CertificateAuthority,
}

impl DiceAttester {
    fn create(
        dice_data: DiceData,
        _application_public_keys: Option<ApplicationPublicKeys>,
    ) -> anyhow::Result<Self> {
        let mut evidence = dice_data
            .evidence
            .context("no evidence provided in DICE data")?;

        // Add next layer evidence.
        let next_layer_evidence = LayerEvidence {
            layer_name: "".to_string(),
            // TODO(#4074): Measure the next layer and generate certificates.
            eca_certificate: vec![],
        };
        if let Some(_application_public_keys) = _application_public_keys {
            // TODO(#4074): Generate application keys certificates.
            let application_keys_certificates = ApplicationKeys {
                encryption_public_key_certificate: Some(vec![]),
                signing_public_key_certificate: Some(vec![]),
            };
            evidence.application_keys = Some(application_keys_certificates);
        }
        evidence.layer_evidence.push(next_layer_evidence);

        Ok(DiceAttester {
            evidence: evidence,
            certificate_authority: dice_data
                .certificate_authority
                .context("no certificate authority provided in DICE data")?,
        })
    }

    fn get_evidence(&self) -> Evidence {
        self.evidence.clone()
    }

    fn generate_dice_data(self) -> anyhow::Result<DiceData> {
        let (eca_private_key, _) = generate_ecdsa_key_pair();
        let next_layer_certificate_authority = CertificateAuthority {
            // TODO(#4074): Create next layer certificate authoruty.
            eca_private_key: eca_private_key.to_bytes().as_slice().into(),
        };
        Ok(DiceData {
            evidence: Some(self.get_evidence()),
            certificate_authority: Some(next_layer_certificate_authority),
        })
    }
}
