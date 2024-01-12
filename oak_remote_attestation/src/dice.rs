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

use crate::proto::oak::attestation::v1::{
    ApplicationKeys, CertificateAuthority, DiceData, Evidence, LayerEvidence, RootLayerEvidence,
    TeePlatform,
};
use alloc::{vec, vec::Vec};
use anyhow::{anyhow, Context};
use coset::{
    cwt::{ClaimName, ClaimsSet},
    CborSerializable,
};
use oak_dice::{
    cert::{
        generate_ecdsa_key_pair, generate_kem_certificate, generate_signing_certificate,
        get_claims_set_from_certificate_bytes,
    },
    evidence::Stage0DiceData,
};
use p256::ecdsa::{SigningKey, VerifyingKey};
use zeroize::Zeroize;

/// Builds the DICE evidence and certificate authority for the next DICE layer.
pub struct DiceBuilder {
    evidence: Evidence,
    signing_key: SigningKey,
}

impl DiceBuilder {
    /// Adds an additional layer of evidence to the DICE data.
    ///
    /// The evidence is in the form of a CWT certificate that contains the `additional_claims`
    /// provided. Adding a layer generates a new ECA private key for the layer and uses it to
    /// replace the existing signing key. The CWT certificate contains the public key for this new
    /// signing key.
    pub fn add_layer(
        &mut self,
        additional_claims: Vec<(ClaimName, ciborium::Value)>,
    ) -> anyhow::Result<()> {
        // The last evidence layer contains the certificate for the current signing key. Since the
        // builder contains an existing signing key there must be at least one layer of evidence
        // that contains the certificate.
        let claims_set = self
            .evidence
            .layers
            .last()
            .ok_or_else(|| anyhow::anyhow!("no evidence layers found"))?
            .get_claims()
            .context("couldn't get layer claims set")?;
        // The issuer for the next layer is the subject of the current last layer.
        let issuer_id = claims_set
            .subject
            .ok_or_else(|| anyhow!("no subject in certificate"))?;

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
        // Replacing the signing key will cause the previous signing key to be dropped, which will
        // zero out its memory.
        self.signing_key = signing_key;
        Ok(())
    }

    /// Adds the CWT certificates application keys to the DICE data.
    ///
    /// Since no additional evidence can be added after the application keys are added, this
    /// consumes DICE data, discards the signing key and returns the finalized evidence.
    pub fn add_application_keys(
        self,
        additional_claims: Vec<(ClaimName, ciborium::Value)>,
        kem_public_key: &[u8],
        verifying_key: &VerifyingKey,
    ) -> anyhow::Result<Evidence> {
        // The last evidence layer contains the certificate for the current signing key. Since the
        // builder contains an existing signing key there must be at least one layer of evidence
        // that contains the certificate.
        let claims_set = self
            .evidence
            .layers
            .last()
            .ok_or_else(|| anyhow::anyhow!("no evidence layers found"))?
            .get_claims()
            .context("couldn't get layer claims set")?;
        // The issuer for the application keys is the subject of the final layer.
        let issuer_id = claims_set
            .subject
            .ok_or_else(|| anyhow!("no subject in certificate"))?;

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
            issuer_id,
            verifying_key,
            additional_claims,
        )
        .map_err(anyhow::Error::msg)
        .context("couldn't generate signing public key certificate")?
        .to_vec()
        .map_err(anyhow::Error::msg)?;

        evidence.application_keys = Some(ApplicationKeys {
            encryption_public_key_certificate,
            signing_public_key_certificate,
        });

        Ok(evidence)
    }
}

impl Drop for DiceData {
    fn drop(&mut self) {
        // Zero out the ECA private key if it was set.
        if let Some(certificate_authority) = &mut self.certificate_authority {
            certificate_authority.eca_private_key.zeroize();
        }
    }
}

impl From<DiceBuilder> for DiceData {
    fn from(value: DiceBuilder) -> Self {
        DiceData {
            evidence: Some(value.evidence),
            certificate_authority: Some(CertificateAuthority {
                eca_private_key: value.signing_key.to_bytes().as_slice().into(),
            }),
        }
    }
}

impl TryFrom<DiceData> for DiceBuilder {
    type Error = anyhow::Error;
    fn try_from(value: DiceData) -> anyhow::Result<Self> {
        let evidence = value
            .evidence
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("no evidence"))?;
        let eca_private_key = &value
            .certificate_authority
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("no certificate authority"))?
            .eca_private_key;
        let signing_key = SigningKey::from_slice(eca_private_key).map_err(anyhow::Error::msg)?;

        Ok(DiceBuilder {
            evidence: evidence.clone(),
            signing_key: signing_key.clone(),
        })
    }
}

impl TryFrom<Stage0DiceData> for DiceData {
    type Error = anyhow::Error;
    fn try_from(value: Stage0DiceData) -> anyhow::Result<Self> {
        let mut layers = Vec::new();
        let eca_certificate =
            oak_dice::utils::cbor_encoded_bytes_to_vec(&value.layer_1_evidence.eca_certificate[..])
                .map_err(anyhow::Error::msg)?;
        layers.push(LayerEvidence { eca_certificate });
        let root_layer = Some(value.root_layer_evidence.try_into()?);
        let layers = vec![value.layer_1_evidence.try_into()?];
        let application_keys = None;
        let evidence = Some(Evidence {
            root_layer,
            layers,
            application_keys,
        });
        let certificate_authority = Some(CertificateAuthority {
            eca_private_key: value.layer_1_certificate_authority.eca_private_key
                [..oak_dice::evidence::P256_PRIVATE_KEY_SIZE]
                .to_vec(),
        });

        Ok(DiceData {
            evidence,
            certificate_authority,
        })
    }
}

impl From<oak_dice::evidence::TeePlatform> for TeePlatform {
    fn from(src: oak_dice::evidence::TeePlatform) -> Self {
        match src {
            oak_dice::evidence::TeePlatform::AmdSevSnp => TeePlatform::AmdSevSnp,
            oak_dice::evidence::TeePlatform::IntelTdx => TeePlatform::IntelTdx,
            oak_dice::evidence::TeePlatform::Unspecified => TeePlatform::Unspecified,
        }
    }
}

impl TryFrom<oak_dice::evidence::Evidence> for Evidence {
    type Error = anyhow::Error;
    fn try_from(value: oak_dice::evidence::Evidence) -> anyhow::Result<Self> {
        let root_layer = Some(value.root_layer_evidence.try_into()?);
        let layers = vec![value.restricted_kernel_evidence.try_into()?];
        let application_keys = Some(value.application_keys.try_into()?);
        Ok(Evidence {
            root_layer,
            layers,
            application_keys,
        })
    }
}

impl TryFrom<oak_dice::evidence::RootLayerEvidence> for RootLayerEvidence {
    type Error = anyhow::Error;
    fn try_from(value: oak_dice::evidence::RootLayerEvidence) -> anyhow::Result<Self> {
        let platform: TeePlatform = value.get_tee_platform().map_err(anyhow::Error::msg)?.into();
        let remote_attestation_report = value
            .get_remote_attestation_report()
            .map_err(anyhow::Error::msg)?
            .to_vec();
        let eca_public_key = value.get_eca_public_key().map_err(anyhow::Error::msg)?;
        Ok(RootLayerEvidence {
            platform: platform as i32,
            remote_attestation_report,
            eca_public_key,
        })
    }
}

impl TryFrom<oak_dice::evidence::LayerEvidence> for LayerEvidence {
    type Error = anyhow::Error;
    fn try_from(value: oak_dice::evidence::LayerEvidence) -> anyhow::Result<Self> {
        let eca_certificate =
            oak_dice::utils::cbor_encoded_bytes_to_vec(&value.eca_certificate[..])
                .map_err(anyhow::Error::msg)?;
        Ok(LayerEvidence { eca_certificate })
    }
}

impl TryFrom<oak_dice::evidence::ApplicationKeys> for ApplicationKeys {
    type Error = anyhow::Error;
    fn try_from(value: oak_dice::evidence::ApplicationKeys) -> anyhow::Result<Self> {
        let encryption_public_key_certificate = oak_dice::utils::cbor_encoded_bytes_to_vec(
            &value.encryption_public_key_certificate[..],
        )
        .map_err(anyhow::Error::msg)?;
        let signing_public_key_certificate =
            oak_dice::utils::cbor_encoded_bytes_to_vec(&value.signing_public_key_certificate[..])
                .map_err(anyhow::Error::msg)?;
        Ok(ApplicationKeys {
            encryption_public_key_certificate,
            signing_public_key_certificate,
        })
    }
}

impl LayerEvidence {
    /// Extracts the `ClaimsSet` encoded in the ECA certificate of the layer.
    pub fn get_claims(&self) -> anyhow::Result<ClaimsSet> {
        get_claims_set_from_certificate_bytes(&self.eca_certificate).map_err(anyhow::Error::msg)
    }
}
