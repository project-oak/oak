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

use oak_sev_guest::{
    guest::{AttestationReport, AttestationRequest, AttestationResponse, ReportStatus},
    msr::SevStatus,
};

use crate::sev::{init_guest_message_encryptor, send_guest_message_request};

/// Returns an attestation report using AMD SEV-SNP.
///
/// If AMD SEV-SNP is enabled it returns a valid hardware-rooted attestation report. In other cases
/// it generates an empty attestation report for testing. The additional data will be set in both
/// cases to bind the DICE chain to the attestation report.
///
/// # Arguments
///
/// * `report_data` - The custom data that must be included in the report. This is typically used to
///   bind information (such as the hash of a public key) to the report.
pub fn get_attestation(
    report_data: [u8; oak_stage0_dice::REPORT_DATA_SIZE],
) -> Result<AttestationReport, &'static str> {
    if crate::sev_status().contains(SevStatus::SNP_ACTIVE) {
        let mut guest_message_encryptor = init_guest_message_encryptor()?;
        let mut report_request = AttestationRequest::new();
        report_request.report_data = report_data;
        let attestation_response: AttestationResponse =
            send_guest_message_request(&mut guest_message_encryptor, report_request)?;
        attestation_response.validate()?;
        if attestation_response.get_status() != Some(ReportStatus::Success) {
            return Err("report request failed due to invalid parameters");
        }
        Ok(attestation_response.report)
    } else {
        oak_stage0_dice::mock_attestation_report(report_data)
    }
}
