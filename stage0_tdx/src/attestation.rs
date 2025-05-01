//
// Copyright 2025 The Project Oak Authors
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

use alloc::vec::Vec;

use oak_attestation_types::{
    attester::Attester,
    util::{encode_length_delimited_proto, Serializable},
};
use oak_proto_rust::oak::attestation::v1::{
    CertificateAuthority, DiceData, EventLog, Evidence, RootLayerEvidence, TeePlatform,
};
use oak_tdx_guest::tdcall::{extend_rtmr, ExtensionBuffer, RtmrIndex};
use sha2::{Digest, Sha384};

pub struct RtmrAttester {
    evidence: Evidence,
}

impl Default for RtmrAttester {
    fn default() -> Self {
        let event_log = EventLog::default();
        let root_layer = RootLayerEvidence {
            platform: TeePlatform::IntelTdx as i32,
            remote_attestation_report: Vec::default(),
            eca_public_key: Vec::default(),
        };

        let evidence = Evidence {
            root_layer: Some(root_layer),
            layers: Vec::new(),
            application_keys: None,
            event_log: Some(event_log),
        };

        Self { evidence }
    }
}

impl Attester for RtmrAttester {
    fn extend(&mut self, encoded_event: &[u8]) -> anyhow::Result<()> {
        self.evidence
            .event_log
            .get_or_insert_with(EventLog::default)
            .encoded_events
            .push(encoded_event.to_vec());

        let digest = Sha384::digest(encoded_event);
        // We always extend RTMR2 for all event log entries.
        extend_rtmr(RtmrIndex::Rtmr2, ExtensionBuffer { data: digest.into() })
            .map_err(anyhow::Error::msg)
    }

    fn quote(&self) -> anyhow::Result<Evidence> {
        anyhow::bail!("Not implemented");
    }
}

impl Serializable for RtmrAttester {
    fn deserialize(_bytes: &[u8]) -> anyhow::Result<Self> {
        anyhow::bail!("Not implemented");
    }

    fn serialize(self) -> Vec<u8> {
        // TODO: b/368023328 - Rename DiceData.
        let attestation_data = DiceData {
            evidence: Some(self.evidence),
            certificate_authority: Some(CertificateAuthority { eca_private_key: Vec::default() }),
        };
        encode_length_delimited_proto(&attestation_data)
    }
}
