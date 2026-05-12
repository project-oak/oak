// Copyright 2026 The Project Oak Authors
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

use alloc::{string::String, vec::Vec};

use oak_proto_rust::google::pes::v1::{
    EcdsaP256PublicKey as ProtoEcdsaP256PublicKey, PublicEndorsement as ProtoPublicEndorsement,
    Signature as ProtoSignature, Statement as ProtoStatement, TLogReceipt as ProtoTLogReceipt,
    VerificationMaterial as ProtoVerificationMaterial, X509Der as ProtoX509Der,
    statement::Format as StatementFormat,
    verification_material::VerificationMaterial as ProtoVerificationMaterialEnum,
};
use serde::{Deserialize, Serialize};

mod base64_serde {
    use alloc::{string::String, vec::Vec};

    use base64::{Engine as _, engine::general_purpose::STANDARD};
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        STANDARD.decode(s.trim()).map_err(serde::de::Error::custom)
    }

    pub fn serialize<S>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let s = STANDARD.encode(bytes);
        serializer.serialize_str(&s)
    }
}

/// JSON representation structure with exactly the same fields as
/// `PublicEndorsement` but with serde json conversion annotations.
#[derive(Deserialize, Serialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct PublicEndorsement {
    pub name: Option<String>,
    pub statement: Option<Statement>,
    pub statement_signature: Option<Signature>,
    pub endorsement_signatures: Option<Vec<Signature>>,
    pub tlog_receipt: Option<TLogReceipt>,
}

#[derive(Deserialize, Serialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct Statement {
    pub format: Option<String>,
    #[serde(with = "base64_serde")]
    pub serialized: Vec<u8>,
}

#[derive(Deserialize, Serialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct Signature {
    #[serde(with = "base64_serde")]
    pub signature: Vec<u8>,
    pub verification_material: Option<VerificationMaterial>,
}

#[derive(Deserialize, Serialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct VerificationMaterial {
    pub x509_certificate: Option<X509Der>,
    pub ecdsa_p256_sha256: Option<EcdsaP256PublicKey>,
}

#[derive(Deserialize, Serialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct X509Der {
    #[serde(with = "base64_serde")]
    pub der_bytes: Vec<u8>,
}

#[derive(Deserialize, Serialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaP256PublicKey {
    #[serde(with = "base64_serde")]
    pub der_bytes: Vec<u8>,
}

#[derive(Deserialize, Serialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct TLogReceipt {
    pub entry_id: Option<String>,
}

impl TryFrom<&[u8]> for PublicEndorsement {
    type Error = anyhow::Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        serde_json::from_slice(bytes).map_err(Into::into)
    }
}

impl From<PublicEndorsement> for ProtoPublicEndorsement {
    fn from(value: PublicEndorsement) -> Self {
        let name = value.name.unwrap_or_default();
        let statement = value.statement.map(ProtoStatement::from);
        let statement_signature = value.statement_signature.map(ProtoSignature::from);
        let endorsement_signatures = value
            .endorsement_signatures
            .unwrap_or_default()
            .into_iter()
            .map(ProtoSignature::from)
            .collect();
        let tlog_receipt = value.tlog_receipt.map(ProtoTLogReceipt::from);

        ProtoPublicEndorsement {
            name,
            statement,
            statement_signature,
            endorsement_signatures,
            tlog_receipt,
        }
    }
}

impl From<Statement> for ProtoStatement {
    fn from(value: Statement) -> Self {
        let format = match value.format.as_deref() {
            Some("JSON_INTOTO") => StatementFormat::JsonIntoto.into(),
            _ => StatementFormat::Unspecified.into(),
        };
        ProtoStatement { format, serialized: value.serialized }
    }
}

impl From<Signature> for ProtoSignature {
    fn from(value: Signature) -> Self {
        let verification_material =
            value.verification_material.map(ProtoVerificationMaterial::from);
        ProtoSignature { signature: value.signature, verification_material }
    }
}

impl From<VerificationMaterial> for ProtoVerificationMaterial {
    fn from(value: VerificationMaterial) -> Self {
        let vm = if let Some(x509) = value.x509_certificate {
            Some(ProtoVerificationMaterialEnum::X509Certificate(ProtoX509Der::from(x509)))
        } else {
            value.ecdsa_p256_sha256.map(|ecdsa| {
                ProtoVerificationMaterialEnum::EcdsaP256Sha256(ProtoEcdsaP256PublicKey::from(ecdsa))
            })
        };
        ProtoVerificationMaterial { verification_material: vm }
    }
}

impl From<X509Der> for ProtoX509Der {
    fn from(value: X509Der) -> Self {
        ProtoX509Der { der_bytes: value.der_bytes }
    }
}

impl From<EcdsaP256PublicKey> for ProtoEcdsaP256PublicKey {
    fn from(value: EcdsaP256PublicKey) -> Self {
        ProtoEcdsaP256PublicKey { der_bytes: value.der_bytes }
    }
}

impl From<TLogReceipt> for ProtoTLogReceipt {
    fn from(value: TLogReceipt) -> Self {
        ProtoTLogReceipt { entry_id: value.entry_id.unwrap_or_default() }
    }
}
