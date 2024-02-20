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

use oak_sev_snp_attestation_report::AttestationReport;
use oak_sev_snp_guest::{
    guest::{
        AttestationRequest, AttestationResponse, GuestFieldFlags, KeyRequest, KeyResponse,
        ReportStatus,
    },
    msr::SevStatus,
};

use crate::sev::send_guest_message_request;

type DerivedKey = [u8; 32];

// The number of bytes of custom data that can be included in the attestation report.
const REPORT_DATA_SIZE: usize = 64;

/// Returns an attestation report.
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
    report_data: [u8; REPORT_DATA_SIZE],
) -> Result<AttestationReport, &'static str> {
    if crate::sev_status().contains(SevStatus::SNP_ACTIVE) {
        let mut report_request = AttestationRequest::new();
        report_request.report_data = report_data;
        let attestation_response: AttestationResponse = send_guest_message_request(report_request)?;
        attestation_response.validate()?;
        if attestation_response.get_status() != Some(ReportStatus::Success) {
            return Err("report request failed due to invalid parameters");
        }
        Ok(attestation_response.report)
    } else {
        oak_stage0_dice::mock_attestation_report(report_data)
    }
}

/// Requests a derived key.
///
/// The key is derived from the VCEK. The key derivation mixes in the VM launch measurement and
/// guest policy and uses VMPL0.
///
/// We use this key as the unique device secret for deriving compound devices identifiers for each
/// layer, and eventually a sealing key in the last layer.
pub fn get_derived_key() -> Result<DerivedKey, &'static str> {
    if crate::sev_status().contains(SevStatus::SNP_ACTIVE) {
        let mut key_request = KeyRequest::new();
        let selected_fields = GuestFieldFlags::MEASUREMENT | GuestFieldFlags::GUEST_POLICY;
        key_request.guest_field_select = selected_fields.bits();
        let key_response: KeyResponse = send_guest_message_request(key_request)?;
        Ok(key_response.derived_key)
    } else {
        oak_stage0_dice::mock_derived_key()
    }
}
