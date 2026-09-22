//
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

//! Wrapping a statement in the attestation that vouches for it.

use std::{collections::BTreeMap, fs, path::Path};

use anyhow::{Context, Result, anyhow};
use base64::{Engine, engine::general_purpose::STANDARD as BASE64};
use oak_attestation_types::assertion_generator::AssertionGenerator;
use oak_proto_rust::oak::attestation::v1::Assertion;
use prost::Message;
use serde::{Deserialize, Serialize};

use crate::statement::InTotoStatement;

pub const PAYLOAD_TYPE: &str = "application/vnd.in-toto+json";

/// Key under which the token is stored in [`Envelope::assertions`].
/// Denotes a Confidential Space token whose `eat_nonce` commits to the payload
/// digest. A random UUID, as Oak names assertion types in
/// `oak_proto_rust::attestation`.
pub const ASSERTION_ID: &str = "49128794-6056-4999-ab3b-00d22d8c2eee";

/// An in-toto Statement together with assertions about it.
///
/// Not DSSE: Confidential Space returns a token whose nonce commits to the
/// payload digest, not a detached signature. The cost is that `payloadType`
/// sits outside the signed bytes, and standard in-toto tooling cannot read
/// this envelope.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Envelope {
    pub payload_type: String,
    /// Base64 [`InTotoStatement`], kept opaque because assertions bind the
    /// digest of these exact bytes, which re-serialization would not preserve.
    pub payload: String,
    /// Base64 `oak.attestation.v1.Assertion` protos. Empty when the statement
    /// was produced outside a TEE, which no verifier accepts.
    pub assertions: BTreeMap<String, String>,
}

impl Envelope {
    /// Serializes `statement` once and asserts those exact bytes. Without a
    /// generator, emits an unsigned envelope for testing outside a TEE.
    pub fn new(
        statement: &InTotoStatement,
        generator: Option<&dyn AssertionGenerator>,
    ) -> Result<Self> {
        let payload = serde_json::to_vec(statement).context("serializing the statement")?;
        let mut assertions = BTreeMap::new();
        if let Some(generator) = generator {
            let assertion = generator
                .generate(&payload)
                .map_err(|e| anyhow!("generating an assertion: {e:?}"))?;
            assertions.insert(ASSERTION_ID.to_string(), BASE64.encode(assertion.encode_to_vec()));
        }
        Ok(Self {
            payload_type: PAYLOAD_TYPE.to_string(),
            payload: BASE64.encode(&payload),
            assertions,
        })
    }

    /// Recovers the exact bytes that were asserted, along with what they
    /// encode.
    pub fn decode_payload(&self) -> Result<(Vec<u8>, InTotoStatement)> {
        let payload =
            BASE64.decode(&self.payload).map_err(|e| anyhow!("decoding the payload: {e}"))?;
        let statement =
            serde_json::from_slice(&payload).context("parsing the in-toto Statement")?;
        Ok((payload, statement))
    }

    /// Extracts the Confidential Space assertion. Looked up by ID, because
    /// requiring every entry in the map to pass would accept an unsigned
    /// envelope vacuously.
    pub fn decode_assertion(&self) -> Result<Assertion> {
        let encoded = self
            .assertions
            .get(ASSERTION_ID)
            .ok_or_else(|| anyhow!("the envelope carries no Confidential Space assertion"))?;
        let bytes = BASE64.decode(encoded).map_err(|e| anyhow!("decoding the assertion: {e}"))?;
        Assertion::decode(bytes.as_slice()).context("parsing the assertion")
    }

    pub fn read(path: &Path) -> Result<Self> {
        let bytes = fs::read(path).with_context(|| format!("reading {}", path.display()))?;
        serde_json::from_slice(&bytes).context("parsing the envelope")
    }

    /// Writes pretty JSON, since people read and diff these too.
    pub fn write(&self, path: &Path) -> Result<()> {
        let mut bytes = serde_json::to_vec_pretty(self).context("serializing the envelope")?;
        bytes.push(b'\n');
        fs::write(path, bytes).with_context(|| format!("writing {}", path.display()))
    }
}
