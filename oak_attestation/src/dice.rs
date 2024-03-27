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

use alloc::{vec, vec::Vec};

use anyhow::{anyhow, Context};
use coset::{cwt::ClaimName, CborSerializable};
use oak_dice::{
    cert::{
        generate_ecdsa_key_pair, generate_kem_certificate, generate_signing_certificate,
        get_claims_set_from_certificate_bytes,
    },
    evidence::Stage0DiceData,
};
use p256::ecdsa::{SigningKey, VerifyingKey};
use zeroize::Zeroize;

use crate::proto::oak::attestation::v1::{
    ApplicationKeys, CertificateAuthority, DiceData, Evidence, LayerEvidence, RootLayerEvidence,
    TeePlatform,
};

/// Builds the DICE evidence and certificate authority for the next DICE layer.
pub struct DiceBuilder {
    evidence: Evidence,
    signing_key: SigningKey,
}

impl DiceBuilder {
    /// Adds an additional layer of evidence to the DICE data.
    ///
    /// The evidence is in the form of a CWT certificate that contains the
    /// `additional_claims` provided. Adding a layer generates a new ECA
    /// private key for the layer and uses it to replace the existing
    /// signing key. The CWT certificate contains the public key for this new
    /// signing key.
    pub fn add_layer(
        &mut self,
        additional_claims: Vec<(ClaimName, ciborium::Value)>,
    ) -> anyhow::Result<()> {
        // The last evidence layer contains the certificate for the current signing key.
        // Since the builder contains an existing signing key there must be at
        // least one layer of evidence that contains the certificate.

        let layer_evidence = self
            .evidence
            .layers
            .last()
            .ok_or_else(|| anyhow::anyhow!("no evidence layers found"))?;
        let claims_set = get_claims_set_from_certificate_bytes(&layer_evidence.eca_certificate)
            .map_err(anyhow::Error::msg)?;

        // The issuer for the next layer is the subject of the current last layer.
        let issuer_id = claims_set.subject.ok_or_else(|| anyhow!("no subject in certificate"))?;

        let evidence = &mut self.evidence;
        let (signing_key, verifying_key) = generate_ecdsa_key_pair();

        let eca_certificate = generate_signing_certificate(
            &self.signing_key,
            issuer_id,
            &verifying_key,
            additional_claims,
        )
        .map_err(anyhow::Error::msg)
        .context("couldn't generate ECA certificate for the next layer")?;
        evidence.layers.push(LayerEvidence {
            eca_certificate: eca_certificate.to_vec().map_err(anyhow::Error::msg)?,
        });
        // Replacing the signing key will cause the previous signing key to be dropped,
        // which will zero out its memory.
        self.signing_key = signing_key;
        Ok(())
    }

    /// Adds the CWT certificates application keys to the DICE data.
    ///
    /// Since no additional evidence can be added after the application keys are
    /// added, this consumes DICE data, discards the signing key and returns
    /// the finalized evidence.
    pub fn add_application_keys(
        self,
        additional_claims: Vec<(ClaimName, ciborium::Value)>,
        kem_public_key: &[u8],
        verifying_key: &VerifyingKey,
        group_kem_public_key: Option<&[u8]>,
        group_verifying_key: Option<&VerifyingKey>,
    ) -> anyhow::Result<Evidence> {
        // The last evidence layer contains the certificate for the current signing key.
        // Since the builder contains an existing signing key there must be at
        // least one layer of evidence that contains the certificate.

        let layer_evidence = self
            .evidence
            .layers
            .last()
            .ok_or_else(|| anyhow::anyhow!("no evidence layers found"))?;
        let claims_set = get_claims_set_from_certificate_bytes(&layer_evidence.eca_certificate)
            .map_err(anyhow::Error::msg)?;

        // The issuer for the application keys is the subject of the final layer.
        let issuer_id = claims_set.subject.ok_or_else(|| anyhow!("no subject in certificate"))?;

        let mut evidence = self.evidence;

        let encryption_public_key_certificate = generate_kem_certificate(
            &self.signing_key,
            issuer_id.clone(),
            kem_public_key,
            additional_claims.clone(),
        )
        .map_err(anyhow::Error::msg)
        .context("couldn't generate encryption public key certificate")?
        .to_vec()
        .map_err(anyhow::Error::msg)?;

        let signing_public_key_certificate = generate_signing_certificate(
            &self.signing_key,
            issuer_id.clone(),
            verifying_key,
            additional_claims,
        )
        .map_err(anyhow::Error::msg)
        .context("couldn't generate signing public key certificate")?
        .to_vec()
        .map_err(anyhow::Error::msg)?;

        // Generate group keys certificates as part of Key Provisioning.
        let group_encryption_public_key_certificate =
            if let Some(group_kem_public_key) = group_kem_public_key {
                generate_kem_certificate(
                    &self.signing_key,
                    issuer_id.clone(),
                    group_kem_public_key,
                    vec![],
                )
                .map_err(anyhow::Error::msg)
                .context("couldn't generate encryption public key certificate")?
                .to_vec()
                .map_err(anyhow::Error::msg)?
            } else {
                vec![]
            };

        let group_signing_public_key_certificate =
            if let Some(group_verifying_key) = group_verifying_key {
                generate_signing_certificate(
                    &self.signing_key,
                    issuer_id.clone(),
                    group_verifying_key,
                    vec![],
                )
                .map_err(anyhow::Error::msg)
                .context("couldn't generate signing public key certificate")?
                .to_vec()
                .map_err(anyhow::Error::msg)?
            } else {
                vec![]
            };

        evidence.application_keys = Some(ApplicationKeys {
            encryption_public_key_certificate,
            signing_public_key_certificate,
            group_encryption_public_key_certificate,
            group_signing_public_key_certificate,
        });

        Ok(evidence)
    }

    pub fn serialize(self) -> DiceData {
        DiceData {
            evidence: Some(self.evidence),
            certificate_authority: Some(CertificateAuthority {
                eca_private_key: self.signing_key.to_bytes().as_slice().into(),
            }),
        }
    }
}

impl TryFrom<DiceData> for DiceBuilder {
    type Error = anyhow::Error;
    fn try_from(mut value: DiceData) -> anyhow::Result<Self> {
        let evidence = value.evidence.as_ref().ok_or_else(|| anyhow::anyhow!("no evidence"))?;
        let eca_private_key = &value
            .certificate_authority
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("no certificate authority"))?
            .eca_private_key;
        let signing_key = SigningKey::from_slice(eca_private_key).map_err(anyhow::Error::msg)?;

        // Zero out the ECA private key if it was set.
        if let Some(certificate_authority) = &mut value.certificate_authority {
            certificate_authority.eca_private_key.zeroize();
        }

        Ok(DiceBuilder { evidence: evidence.clone(), signing_key: signing_key.clone() })
    }
}

pub fn stage0_dice_data_to_proto(value: Stage0DiceData) -> anyhow::Result<DiceData> {
    let mut layers = Vec::new();
    let eca_certificate =
        oak_dice::utils::cbor_encoded_bytes_to_vec(&value.layer_1_evidence.eca_certificate[..])
            .map_err(anyhow::Error::msg)?;
    layers.push(LayerEvidence { eca_certificate });
    let root_layer = Some(root_layer_evidence_to_proto(value.root_layer_evidence)?);
    let layers = vec![layer_evidence_to_proto(value.layer_1_evidence)?];
    let application_keys = None;
    let evidence = Some(Evidence { root_layer, layers, application_keys });
    let certificate_authority = Some(CertificateAuthority {
        eca_private_key: value.layer_1_certificate_authority.eca_private_key
            [..oak_dice::evidence::P256_PRIVATE_KEY_SIZE]
            .to_vec(),
    });

    Ok(DiceData { evidence, certificate_authority })
}

fn tee_platform_to_proto(src: oak_dice::evidence::TeePlatform) -> TeePlatform {
    match src {
        oak_dice::evidence::TeePlatform::Unspecified => TeePlatform::Unspecified,
        oak_dice::evidence::TeePlatform::AmdSevSnp => TeePlatform::AmdSevSnp,
        oak_dice::evidence::TeePlatform::IntelTdx => TeePlatform::IntelTdx,
        oak_dice::evidence::TeePlatform::None => TeePlatform::None,
    }
}

pub fn evidence_to_proto(value: oak_dice::evidence::Evidence) -> anyhow::Result<Evidence> {
    let root_layer = Some(root_layer_evidence_to_proto(value.root_layer_evidence)?);
    let layers = vec![layer_evidence_to_proto(value.restricted_kernel_evidence)?];
    let application_keys = Some(application_keys_to_proto(value.application_keys)?);
    Ok(Evidence { root_layer, layers, application_keys })
}

fn root_layer_evidence_to_proto(
    value: oak_dice::evidence::RootLayerEvidence,
) -> anyhow::Result<RootLayerEvidence> {
    let platform: TeePlatform =
        tee_platform_to_proto(value.get_tee_platform().map_err(anyhow::Error::msg)?);
    let remote_attestation_report =
        value.get_remote_attestation_report().map_err(anyhow::Error::msg)?.to_vec();
    let eca_public_key = value.get_eca_public_key().map_err(anyhow::Error::msg)?;
    Ok(RootLayerEvidence { platform: platform as i32, remote_attestation_report, eca_public_key })
}

fn layer_evidence_to_proto(
    value: oak_dice::evidence::LayerEvidence,
) -> anyhow::Result<LayerEvidence> {
    let eca_certificate = oak_dice::utils::cbor_encoded_bytes_to_vec(&value.eca_certificate[..])
        .map_err(anyhow::Error::msg)?;
    Ok(LayerEvidence { eca_certificate })
}

fn application_keys_to_proto(
    value: oak_dice::evidence::ApplicationKeys,
) -> anyhow::Result<ApplicationKeys> {
    let encryption_public_key_certificate =
        oak_dice::utils::cbor_encoded_bytes_to_vec(&value.encryption_public_key_certificate[..])
            .map_err(anyhow::Error::msg)?;
    let signing_public_key_certificate =
        oak_dice::utils::cbor_encoded_bytes_to_vec(&value.signing_public_key_certificate[..])
            .map_err(anyhow::Error::msg)?;
    Ok(ApplicationKeys {
        encryption_public_key_certificate,
        signing_public_key_certificate,
        group_encryption_public_key_certificate: vec![],
        group_signing_public_key_certificate: vec![],
    })
}
