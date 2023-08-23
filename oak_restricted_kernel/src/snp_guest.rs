//
// Copyright 2022 The Project Oak Authors
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

use crate::snp::send_guest_message_request;
pub use oak_sev_guest::guest::{
    AttestationReport, AttestationReportData, AuthorKey, EcdsaSignature, GuestPolicy, TcbVersion,
};
use oak_sev_guest::guest::{
    AttestationRequest, AttestationResponse, GuestFieldFlags, KeyRequest, KeyResponse, ReportStatus,
};

// The number of custom bytes that can be included in the attestation report.
const REPORT_DATA_SIZE: usize = 64;

/// Requests an attestation report.
///
/// # Arguments
///
/// * `report_data` - The custom data that must be included in the report. This is typically used to
///   bind information (such as the hash of a public key) to the report.
pub fn get_attestation(report_data: [u8; REPORT_DATA_SIZE]) -> anyhow::Result<AttestationReport> {
    let mut report_request = AttestationRequest::new();
    report_request.report_data = report_data;
    let attestation_response: AttestationResponse = send_guest_message_request(report_request)?;
    attestation_response
        .validate()
        .map_err(anyhow::Error::msg)?;
    if attestation_response.status != ReportStatus::Success as u32 {
        anyhow::bail!("report request failed due to invalid parameters");
    }
    Ok(attestation_response.report)
}

/// Requests a derived key.
///
/// The key is derived from the VCEK. The key derivation mixes in the VM launch measurement and
/// guest policy and uses VMPL0.
pub fn get_derived_key() -> anyhow::Result<[u8; 32]> {
    let mut key_request = KeyRequest::new();
    let selected_fields = GuestFieldFlags::MEASUREMENT.union(GuestFieldFlags::GUEST_POLICY);
    key_request.guest_field_select = selected_fields.bits();
    let key_response: KeyResponse = send_guest_message_request(key_request)?;
    Ok(key_response.derived_key)
}
