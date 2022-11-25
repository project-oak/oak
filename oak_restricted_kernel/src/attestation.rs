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

use crate::{
    ghcb::GHCB_PROTOCOL, mm::Translator, snp::GUEST_MESSAGE_ENCRYPTOR, ADDRESS_TRANSLATOR,
    GUEST_HOST_HEAP,
};
use alloc::boxed::Box;
pub use oak_sev_guest::guest::{
    AttestationReport, AttestationReportData, AuthorKey, EcdsaSignature, GuestPolicy, TcbVersion,
};
use oak_sev_guest::guest::{AttestationRequest, AttestationResponse, GuestMessage, ReportStatus};
use x86_64::VirtAddr;

// The number of custom bytes that can be included in the attestation report.
const REPORT_DATA_SIZE: usize = 64;

/// Requests an attestation rerport.
///
/// # Arguments
///
/// * `report_data` - The custom data that must be included in the report. This is typically used to
///   bind information (such as the hash of a public key) to the report.
pub fn get_attestation(report_data: [u8; REPORT_DATA_SIZE]) -> anyhow::Result<AttestationReport> {
    let mut guard = GUEST_MESSAGE_ENCRYPTOR.lock();
    let encryptor = guard
        .as_mut()
        .ok_or_else(|| anyhow::anyhow!("guest message encryptor is not initialized"))?;

    let mut report_request = AttestationRequest::new();
    report_request.report_data = report_data;

    let alloc = GUEST_HOST_HEAP
        .get()
        .ok_or_else(|| anyhow::anyhow!("guest-host heap is not initialized"))?;

    let mut request_message = Box::new_in(GuestMessage::new(), alloc);
    encryptor
        .encrypt_message(report_request, request_message.as_mut())
        .map_err(anyhow::Error::msg)?;
    let response_message = Box::new_in(GuestMessage::new(), alloc);

    let translator = ADDRESS_TRANSLATOR
        .get()
        .ok_or_else(|| anyhow::anyhow!("address translator is not initialized"))?;
    let request_address = translator
        .translate_virtual(VirtAddr::from_ptr(
            request_message.as_ref() as *const GuestMessage
        ))
        .ok_or_else(|| anyhow::anyhow!("couldn't translate request address"))?;
    let response_address = translator
        .translate_virtual(VirtAddr::from_ptr(
            response_message.as_ref() as *const GuestMessage
        ))
        .ok_or_else(|| anyhow::anyhow!("couldn't translate response address"))?;

    GHCB_PROTOCOL
        .get()
        .expect("ghcb not initialized")
        .lock()
        .do_guest_message_request(request_address, response_address)
        .map_err(anyhow::Error::msg)?;

    response_message.validate().map_err(anyhow::Error::msg)?;
    let attestation_response = encryptor
        .decrypt_message::<AttestationResponse>(&response_message)
        .map_err(anyhow::Error::msg)?;
    attestation_response
        .validate()
        .map_err(anyhow::Error::msg)?;
    if attestation_response.status != ReportStatus::Success as u32 {
        anyhow::bail!("report request failed due to invalid parameters");
    }
    Ok(attestation_response.report)
}
