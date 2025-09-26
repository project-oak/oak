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
use oak_proto_rust::oak::attestation::v1::{DiceData, EventLog, Evidence};
use oak_tdx_guest::tdcall::{
    extend_rtmr, get_report, ExtensionBuffer, ExtraDataBuffer, RtmrIndex, TdReportBuffer,
};
use sha2::{Digest, Sha384};

pub struct RtmrAttester {
    evidence: Evidence,
}

impl Default for RtmrAttester {
    fn default() -> Self {
        let event_log = Some(EventLog::default());

        let evidence = Evidence { event_log, ..Default::default() };

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
        log::debug!("Event digest: sha2-384:{}", hex::encode(digest.as_slice()));
        // We always extend RTMR2 for all event log entries.
        extend_rtmr(RtmrIndex::Rtmr2, &ExtensionBuffer { data: digest.into() })
            .map_err(anyhow::Error::msg)?;

        let mut report_buffer = TdReportBuffer::new();
        let extra_data = ExtraDataBuffer { data: [0u8; 64] };
        get_report(&extra_data, &mut report_buffer).map_err(anyhow::Error::msg)?;
        log::debug!("RTMR 2: {}", hex::encode(report_buffer.get_rtmr(RtmrIndex::Rtmr2)));
        Ok(())
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
        let attestation_data =
            DiceData { evidence: Some(self.evidence), certificate_authority: None };
        encode_length_delimited_proto(&attestation_data)
    }
}

#[cfg(test)]
mod tests {
    use oak_attestation_types::util::try_decode_length_delimited_proto;
    use zeroize::Zeroize;

    use super::*;
    #[test]
    pub fn test_attestation_proto_to_struct() {
        let attester = RtmrAttester::default();
        let serialized_data: Vec<u8> = attester.serialize();
        let mut attestation_data = try_decode_length_delimited_proto(&serialized_data).unwrap();
        oak_stage0_dice::dice_data_proto_to_stage0_dice_data(&attestation_data)
            .expect("couldn't create struct from proto");
        // Zero out the copy of the private key in the proto that we just created if it
        // exists.
        if let Some(certificate_authority) = attestation_data.certificate_authority.as_mut() {
            certificate_authority.eca_private_key.zeroize()
        };
    }
}
