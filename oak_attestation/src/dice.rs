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

use alloc::{string::String, vec, vec::Vec};

use anyhow::{anyhow, Context};
use ciborium::Value;
use coset::{cwt::ClaimName, CborSerializable, CoseKey};
use oak_attestation_types::{
    attester::Attester,
    transparent_attester::TransparentAttester,
    util::{encode_length_delimited_proto, try_decode_length_delimited_proto, Serializable},
};
use oak_dice::{
    cert::{
        cose_key_to_verifying_key, derive_verifying_key_id, generate_ecdsa_key_pair,
        generate_kem_certificate, generate_signing_certificate,
        get_claims_set_from_certificate_bytes, SHA2_256_ID,
    },
    evidence::Stage0DiceData,
};
use oak_proto_rust::oak::attestation::v1::{
    ApplicationKeys, CertificateAuthority, DiceData, EventLog, Evidence, LayerEvidence,
    RootLayerEvidence, TeePlatform,
};
use p256::ecdsa::{SigningKey, VerifyingKey};
use prost::Message;
use zeroize::Zeroize;

#[allow(deprecated)]
use crate::ApplicationKeysAttester;
use crate::MeasureDigest;

/// Holds additional claims and the encoded event for a DICE layer.
pub struct LayerData {
    /// Additional claims to include in the CWT certificate for the layer.
    pub additional_claims: Vec<(ClaimName, ciborium::Value)>,
    /// Encoded event associated with the layer.
    pub encoded_event: Vec<u8>,
}

/// Builds the DICE evidence and certificate authority for the next DICE layer.
pub struct DiceAttester {
    evidence: Evidence,
    signing_key: SigningKey,
}

// TODO: b/368030563 - Remove this implementation once all client library
// instances use the applications keys from the event log.
#[allow(deprecated)]
impl ApplicationKeysAttester for DiceAttester {
    /// Adds the CWT certificates application keys to the DICE data.
    ///
    /// Since no additional evidence can be added after the application keys are
    /// added, this consumes DICE data, discards the signing key and returns
    /// the finalized evidence.
    fn add_application_keys(
        self,
        layer_data: LayerData,
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
            layer_data.additional_claims.clone(),
        )
        .map_err(anyhow::Error::msg)
        .context("couldn't generate encryption public key certificate")?
        .to_vec()
        .map_err(anyhow::Error::msg)?;

        let signing_public_key_certificate = generate_signing_certificate(
            &self.signing_key,
            issuer_id.clone(),
            verifying_key,
            layer_data.additional_claims,
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
}

impl Attester for DiceAttester {
    fn extend(&mut self, encoded_event: &[u8]) -> anyhow::Result<()> {
        // The last evidence layer contains the certificate for the current signing key.
        // Since the builder contains an existing signing key there must be at least one
        // layer of evidence that contains the certificate, or a root layer that is
        // bound to the attestation report.
        let issuer_id = get_issuer_id(self)?;
        // Generate a signing key for the next layer.
        let (signing_key, verifying_key) = generate_ecdsa_key_pair();

        // Generate a claim for CWT which contains the event digest.
        let event_digest = MeasureDigest::measure_digest(encoded_event);
        let event_claim = (
            ClaimName::PrivateUse(oak_dice::cert::EVENT_ID),
            Value::Map(vec![(
                Value::Integer(SHA2_256_ID.into()),
                Value::Bytes(event_digest.sha2_256),
            )]),
        );

        // Generate new CWT.
        let eca_certificate = generate_signing_certificate(
            &self.signing_key,
            issuer_id,
            &verifying_key,
            vec![event_claim],
        )
        .map_err(anyhow::Error::msg)
        .context("couldn't generate ECA certificate for the next layer")?;

        // Add new layer to the evidence.
        self.evidence.layers.push(LayerEvidence {
            eca_certificate: eca_certificate.to_vec().map_err(anyhow::Error::msg)?,
        });
        self.evidence
            .event_log
            .get_or_insert_with(EventLog::default)
            .encoded_events
            .push(encoded_event.to_vec());

        // Replacing the signing key will cause the previous signing key to be dropped,
        // which will zero out its memory.
        self.signing_key = signing_key;
        Ok(())
    }

    fn quote(&self) -> anyhow::Result<Evidence> {
        Ok(self.evidence.clone())
    }
}

impl TransparentAttester for DiceAttester {
    fn extend_transparent(
        &mut self,
        original_encoded_event: &[u8],
        transparent_encoded_event: &[u8],
    ) -> anyhow::Result<()> {
        let issuer_id = get_issuer_id(self)?;
        // Generate a signing key for the next layer.
        let (signing_key, verifying_key) = generate_ecdsa_key_pair();

        // Generate a claim for CWT which contains the original event digest.
        let original_event_digest = MeasureDigest::measure_digest(original_encoded_event);
        let original_event_claim = (
            ClaimName::PrivateUse(oak_dice::cert::EVENT_ID),
            Value::Map(vec![(
                Value::Integer(SHA2_256_ID.into()),
                Value::Bytes(original_event_digest.sha2_256),
            )]),
        );

        // Generate a claim for CWT which contains the transparent event digest.
        let transparent_event_digest = MeasureDigest::measure_digest(transparent_encoded_event);
        let transparent_event_claim = (
            ClaimName::PrivateUse(oak_dice::cert::TRANSPARENT_EVENT_ID),
            Value::Map(vec![(
                Value::Integer(SHA2_256_ID.into()),
                Value::Bytes(transparent_event_digest.sha2_256),
            )]),
        );

        // Generate new CWT.
        let eca_certificate = generate_signing_certificate(
            &self.signing_key,
            issuer_id,
            &verifying_key,
            vec![original_event_claim, transparent_event_claim],
        )
        .map_err(anyhow::Error::msg)
        .context("couldn't generate ECA certificate for the next layer")?;

        // Add new layer to the evidence.
        self.evidence.layers.push(LayerEvidence {
            eca_certificate: eca_certificate.to_vec().map_err(anyhow::Error::msg)?,
        });
        // Update the event logs with the appropriate encoded event.
        self.evidence
            .event_log
            .get_or_insert_with(EventLog::default)
            .encoded_events
            .push(original_encoded_event.to_vec());
        self.evidence
            .transparent_event_log
            .get_or_insert_with(EventLog::default)
            .encoded_events
            .push(transparent_encoded_event.to_vec());

        // Replacing the signing key will cause the previous signing key to be dropped,
        // which will zero out its memory.
        self.signing_key = signing_key;
        Ok(())
    }
}

impl Serializable for DiceAttester {
    fn deserialize(bytes: &[u8]) -> anyhow::Result<Self> {
        let dice_data: DiceData =
            try_decode_length_delimited_proto(bytes).context("couldn't parse DICE data: {:?}")?;
        dice_data.try_into()
    }

    fn serialize(self) -> Vec<u8> {
        let dice_data = DiceData {
            evidence: Some(self.evidence),
            certificate_authority: Some(CertificateAuthority {
                eca_private_key: self.signing_key.to_bytes().as_slice().into(),
            }),
        };
        let result = encode_length_delimited_proto(&dice_data);

        // Zero out the ECA private key in the proto.
        dice_data
            .certificate_authority
            .expect("no certificate authority")
            .eca_private_key
            .zeroize();

        result
    }
}

impl TryFrom<DiceData> for DiceAttester {
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

        Ok(DiceAttester { evidence: evidence.clone(), signing_key })
    }
}

pub fn stage0_dice_data_and_event_log_to_proto(
    value: Stage0DiceData,
    event_log: EventLog,
) -> anyhow::Result<DiceData> {
    let mut layers = Vec::new();
    let eca_certificate =
        oak_dice::utils::cbor_encoded_bytes_to_vec(&value.layer_1_evidence.eca_certificate[..])
            .map_err(anyhow::Error::msg)?;
    layers.push(LayerEvidence { eca_certificate });
    let root_layer = Some(root_layer_evidence_to_proto(value.root_layer_evidence)?);
    let layers = vec![layer_evidence_to_proto(value.layer_1_evidence)?];
    let application_keys = None;
    let evidence = Some(Evidence {
        root_layer,
        layers,
        application_keys,
        event_log: Some(event_log),
        transparent_event_log: None,
        signed_user_data_certificate: vec![],
    });
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

pub fn evidence_and_event_log_to_proto(
    value: oak_dice::evidence::Evidence,
    encoded_event_log: Option<&[u8]>,
) -> anyhow::Result<Evidence> {
    let root_layer = Some(root_layer_evidence_to_proto(value.root_layer_evidence)?);
    let layers = vec![layer_evidence_to_proto(value.restricted_kernel_evidence)?];
    let application_keys = Some(application_keys_to_proto(value.application_keys)?);
    let event_log = encoded_event_log
        .map(EventLog::decode)
        .transpose()
        .map_err(anyhow::Error::msg)
        .context("couldn't decode event log")?;
    let transparent_event_log: Option<EventLog> = None;
    let signed_user_data_certificate = vec![];
    Ok(Evidence {
        root_layer,
        layers,
        application_keys,
        event_log,
        transparent_event_log,
        signed_user_data_certificate,
    })
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

fn get_issuer_id(dice_attester: &DiceAttester) -> anyhow::Result<String> {
    // The last evidence layer contains the certificate for the current signing key.
    // Since the builder contains an existing signing key there must be at least one
    // layer of evidence that contains the certificate, or a root layer that is
    // bound to the attestation report.
    let issuer_id = match dice_attester
        .evidence
        .layers
        .last()
        .map(|last| {
            get_claims_set_from_certificate_bytes(&last.eca_certificate).map_err(anyhow::Error::msg)
        })
        .transpose()?
        .map(|claims_set| claims_set.subject.ok_or_else(|| anyhow!("no subject in certificate")))
        .transpose()?
    {
        Some(issuer_id) => issuer_id,
        None => {
            let root_layer = dice_attester
                .evidence
                .root_layer
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("no root layer evidence"))?;
            let cose_key = CoseKey::from_slice(root_layer.eca_public_key.as_slice())
                .map_err(anyhow::Error::msg)?;
            let verifying_key = cose_key_to_verifying_key(&cose_key).map_err(anyhow::Error::msg)?;
            hex::encode(derive_verifying_key_id(&verifying_key))
        }
    };
    Ok(issuer_id)
}
