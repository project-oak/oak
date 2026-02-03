//
// Copyright 2024 The Project Oak Authors
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

use oak_attestation::dice::DiceAttester;
use oak_sev_guest::{
    crypto::GuestMessageEncryptor,
    guest::{
        GuestFieldFlags, GuestMessage, Message, ReportStatus,
        v1::{AttestationRequest, AttestationResponse, KeyRequest, KeyResponse},
    },
    msr::SevStatus,
};
use oak_sev_snp_attestation_report::{AttestationReport, REPORT_DATA_SIZE};
use oak_stage0::{allocator::Shared, hal::Platform};
use oak_stage0_dice::DerivedKey;
use spinning_top::Spinlock;
use x86_64::{PhysAddr, VirtAddr};
use zerocopy::{FromBytes, IntoBytes};
use zeroize::Zeroize;

use super::{GHCB_WRAPPER, SEV_SECRETS};

/// Cryptographic helper to encrypt and decrypt messages for the GHCB guest
/// message protocol.
static GUEST_MESSAGE_ENCRYPTOR: Spinlock<Option<GuestMessageEncryptor>> = Spinlock::new(None);

/// Initializes the Guest Message encryptor using VMPCK0.
pub fn init_guest_message_encryptor() -> Result<(), &'static str> {
    // Safety: `SecretsPage` implements `FromBytes` which ensures that it has no
    // requirements on the underlying bytes.
    let key = &mut unsafe { SEV_SECRETS.assume_init_mut() }.vmpck_0[..];
    GUEST_MESSAGE_ENCRYPTOR.lock().replace(GuestMessageEncryptor::new(key)?);
    // Once the we have read VMPCK0 we wipe it so that later boot stages cannot
    // request attestation reports or derived sealing keys for VMPL0. This stops
    // later boot stages from creating counterfeit DICE chains.
    key.zeroize();
    // The sev-guest driver in the upstream kernel does not initialize with such
    // an empty vmpck. So we fill it up with 0xFF.
    key.fill(0xFF);
    Ok(())
}

/// Sends a request to the Secure Processor using the Guest Message Protocol.
fn send_guest_message_request<
    Request: IntoBytes + FromBytes + Message,
    Response: IntoBytes + FromBytes + Message,
>(
    request: Request,
) -> Result<Response, &'static str> {
    let mut guard = GUEST_MESSAGE_ENCRYPTOR.lock();
    let encryptor = guard.as_mut().ok_or("guest message encryptor is not initialized")?;
    let alloc = &oak_stage0::SHORT_TERM_ALLOC;
    let mut request_message = Shared::<_, _, super::Sev>::new_in(GuestMessage::new(), alloc);
    encryptor.encrypt_message(request, request_message.as_mut())?;
    let response_message = Shared::<_, _, super::Sev>::new_in(GuestMessage::new(), alloc);

    let request_address = PhysAddr::new(VirtAddr::from_ptr(request_message.as_ref()).as_u64());
    let response_address = PhysAddr::new(VirtAddr::from_ptr(response_message.as_ref()).as_u64());

    GHCB_WRAPPER
        .get()
        .ok_or("GHCB not initialized")?
        .do_guest_message_request(request_address, response_address)?;
    response_message.validate()?;
    encryptor.decrypt_message::<Response>(response_message.as_ref())
}

pub fn get_attester() -> Result<DiceAttester, &'static str> {
    oak_stage0_dice::generate_initial_dice_data(
        get_attestation,
        crate::platform::Sev::tee_platform(),
    )?
    .try_into()
    .map_err(|_| "couldn't convert initial DICE evidence to an attester")
}

fn get_attestation(report_data: [u8; REPORT_DATA_SIZE]) -> Result<AttestationReport, &'static str> {
    if super::sev_status().contains(SevStatus::SNP_ACTIVE) {
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

pub fn get_derived_key() -> Result<DerivedKey, &'static str> {
    if super::sev_status().contains(SevStatus::SNP_ACTIVE) {
        let mut key_request = KeyRequest::new();
        let selected_fields = GuestFieldFlags::MEASUREMENT | GuestFieldFlags::GUEST_POLICY;
        key_request.guest_field_select = selected_fields.bits();
        let key_response: KeyResponse = send_guest_message_request(key_request)?;
        Ok(key_response.derived_key)
    } else {
        oak_stage0::hal::Base::get_derived_key()
    }
}
