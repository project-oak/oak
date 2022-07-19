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

//! Rust implementations of the AMD SEV-SNP GHCB MSR protocol.
//!
//! The protocol is implemented by writing to, and reading from, model-specific register (MSR)
//! 0xC001_0130. The guest makes a request by writing an appropriate value to the MSR and calling
//! VMGEXIT. After the hypervisor processes the request and resumes the guest, the guest can read
//! the response from the same MSR.
//!
//! The 12 least significant bits represent information about the operation being performed. The
//! remaining 52 bits represent the data for the operation. The format of the data is dependent on
//! the operation.
//!
//! The MSR protocol is primarily used to set up the GHCB communications with the hypervisor.
//!
//! See section 2.3.1 in <https://developer.amd.com/wp-content/resources/56421.pdf> for more detail.
//!
//! Note: This implementation does not include the AP Reset Hold operations seeing that it is not
//! the preferred mechanism for starting a new application processor (AP) under AMD SEV-SNP. The
//! SEV-SNP AP creation NAE should be used instead. See section 4.3.2 of
//! <https://developer.amd.com/wp-content/resources/56421.pdf>.

use crate::instructions::vmgexit;
use anyhow::{anyhow, bail, Result};
use bitflags::bitflags;
use strum::FromRepr;
use x86_64::registers::model_specific::Msr;

/// The version of the GHCB MSR protocol supported by this library. This represents the version
/// specific to AMD SEV-SNP.
pub const SUPPORTED_PROTOCOL_VERION: u16 = 2;

/// Value indicating that the hypervisor does not have a preferred location for the GHCB.
pub const NO_PREFERRED_GHCB_LOCATION: u64 = 0xFFFFFFFFFFFFF000;

/// Value indicating that the hypervisor did not accept the registered location for the GHCB.
const GHCB_LOCATION_NOT_ACCEPTED: u64 = 0xFFFFFFFFFFFFF000;

/// The identifier for the MSR used in the protocol.
const MSR_IDENTIFIER: u32 = 0xC001_0130;

/// Mask to extract the GHCB info from a u64 value.
const GHCB_INFO_MASK: u64 = 0xFFF;

/// Mask to extract the GHCB data from a u64 value.
const GCHP_DATA_MASK: u64 = !GHCB_INFO_MASK;

/// Contains the guest-physical address of the GHCB page. The address must have been registered with
/// the hypervisor before using it.
pub struct GhcbGpa {
    gpa: u64,
}

impl GhcbGpa {
    pub fn new(gpa: usize) -> Result<Self> {
        let gpa = gpa as u64;
        if gpa & GHCB_INFO_MASK != 0 {
            bail!("GHCB must be 4KiB-aligned");
        }
        Ok(Self { gpa })
    }
}

impl From<GhcbGpa> for u64 {
    fn from(ghcb_gpa: GhcbGpa) -> Self {
        ghcb_gpa.gpa
    }
}

/// Sets the address of the GHCB page before exiting to the hypervisor.
pub fn set_ghcb_address_and_exit(ghcb_gpa: GhcbGpa) {
    write_msr_and_exit(ghcb_gpa.into());
}

/// Response from the hypervisor about the encryption bit and supported GHCB protocol versions. The
/// encryption bit value is validated by the hardware before the guest is resumed.
pub struct SevInfoResponse {
    /// The minimum version of the GHCB MSR protocol supported by the hypervisor.
    pub min_protocol_version: u16,
    /// The maximum version of the GHCB MSR protocol supported by the hypervisor.
    pub max_protocol_version: u16,
    /// The page table bit used for inidicating that a page is encrypted.
    pub encryption_bit: u8,
}

impl TryFrom<u64> for SevInfoResponse {
    type Error = anyhow::Error;
    fn try_from(msr_value: u64) -> Result<Self> {
        const SEV_INFO_RESPONSE_INFO: u64 = 0x001;
        if msr_value & GHCB_INFO_MASK != SEV_INFO_RESPONSE_INFO {
            bail!("Value is not a valid SEV information response");
        }
        let max_protocol_version = (msr_value >> 48) as u16;
        let min_protocol_version = (msr_value >> 32) as u16;
        let encryption_bit = (msr_value >> 24) as u8;
        Ok(Self {
            min_protocol_version,
            max_protocol_version,
            encryption_bit,
        })
    }
}

/// A request for information about the supported GHCB MSR protocol version and the encryption bit.
pub struct SevInfoRequest;

impl From<SevInfoRequest> for u64 {
    fn from(_request: SevInfoRequest) -> Self {
        0x002
    }
}

/// Gets information about the supported GHCB MSR protocol verions and the location of the
/// encryption bit.
pub fn get_sev_info() -> Result<SevInfoResponse> {
    let request = SevInfoRequest;
    write_msr_and_exit(request.into());
    read_msr().try_into()
}

/// The register of interest from the result of executing CPUID.
#[derive(Debug, FromRepr)]
#[repr(u8)]
pub enum CpuidRegister {
    Eax = 0,
    Ebx = 1,
    Ecx = 2,
    Edx = 3,
}

/// A request to execute CPUID for a specific leaf and return one of the result registers.
pub struct CpuidRequest {
    /// The CPUID leaf to request. Sub-leafs are not supported byt this protocol.
    pub leaf: u32,
    /// The register to return from the result. This protocol only supports a single register at a
    /// time.
    pub register: CpuidRegister,
}

impl From<CpuidRequest> for u64 {
    fn from(request: CpuidRequest) -> Self {
        let info = 0x004;
        info | (request.leaf as u64) << 32 | (request.register as u64) << 30
    }
}

/// A response from executing CPUID for a specific leaf. Only one register is returned at a time.
pub struct CpuidResponse {
    /// The value of the requested register after executing CPUID.
    pub value: u32,
    /// The register that the value represents.
    pub register: CpuidRegister,
}

impl TryFrom<u64> for CpuidResponse {
    type Error = anyhow::Error;
    fn try_from(msr_value: u64) -> Result<Self> {
        const SEV_INFO_RESPONSE_INFO: u64 = 0x005;
        const RESERVED_MASK: u64 = 0x3FFFF000;
        if msr_value & GHCB_INFO_MASK != SEV_INFO_RESPONSE_INFO || msr_value & RESERVED_MASK != 0 {
            bail!("Value is not a valid CPUID response");
        }
        let value = (msr_value >> 32) as u32;
        const REGISTER_MASK: u64 = 0xC0000000;
        let register = CpuidRegister::from_repr(((msr_value & REGISTER_MASK) >> 30) as u8)
            .ok_or_else(|| anyhow::anyhow!("Invalid register"))?;
        Ok(Self { value, register })
    }
}

/// Gets the value of the specified register that was returned when executing CPUID for the
/// specified leaf. Sub-leafs are not supported.
pub fn get_cpuid(request: CpuidRequest) -> Result<CpuidResponse> {
    write_msr_and_exit(request.into());
    read_msr().try_into()
}

/// A request for the hypervisor's preferred location for the GHCB page.
pub struct PreferredGhcbGpaRequest;

impl From<PreferredGhcbGpaRequest> for u64 {
    fn from(_request: PreferredGhcbGpaRequest) -> Self {
        0x010
    }
}

/// The response containing the preferred location of the GHCB.
pub struct PreferredGhcbGpaResponse {
    /// The preferred guest-physical address for the GHCB.
    pub ghcb_gpa: usize,
}

impl TryFrom<u64> for PreferredGhcbGpaResponse {
    type Error = anyhow::Error;
    fn try_from(msr_value: u64) -> Result<Self> {
        const PREFERRED_GPA_RESPONSE_INFO: u64 = 0x011;
        if msr_value & GHCB_INFO_MASK != PREFERRED_GPA_RESPONSE_INFO {
            bail!("Value is not a valid preferred GHCP GPA response");
        }
        let ghcb_gpa = (msr_value & GCHP_DATA_MASK) as usize;
        Ok(Self { ghcb_gpa })
    }
}

/// Requests the hypervisor's preferred location for the GHCB page.
///
/// A response of `NO_PREFERRED_GHCB_LOCATION` indicates that the hypervisor does not have a
/// preferred location.
///
/// The guest must validate that the returned guest-physical address is not part of its known
/// guest-private memory.
pub fn get_preferred_ghcb_location() -> Result<PreferredGhcbGpaResponse> {
    let request = PreferredGhcbGpaRequest;
    write_msr_and_exit(request.into());
    read_msr().try_into()
}

/// Request to register a guest-physical address for the GHCB with the hypervisor.
pub struct RegisterGhcbGpaRequest {
    ghcb_gpa: u64,
}

impl RegisterGhcbGpaRequest {
    pub fn new(ghcb_gpa: usize) -> Result<Self> {
        let ghcb_gpa = ghcb_gpa as u64;
        if ghcb_gpa & GHCB_INFO_MASK != 0 {
            bail!("GHCB must be 4KiB-aligned");
        }
        Ok(Self { ghcb_gpa })
    }
}

impl From<RegisterGhcbGpaRequest> for u64 {
    fn from(request: RegisterGhcbGpaRequest) -> Self {
        let info = 0x012;
        info | request.ghcb_gpa
    }
}

/// The response containing the result of the GHCB registration.
pub struct RegisterGhcbGpaResponse {
    /// The registered guest-physical address for the GHCB.
    ghcb_gpa: u64,
}

impl TryFrom<u64> for RegisterGhcbGpaResponse {
    type Error = anyhow::Error;
    fn try_from(msr_value: u64) -> Result<Self> {
        const REGISTER_GHCB_GPA_RESPONSE_INFO: u64 = 0x013;
        if msr_value & GHCB_INFO_MASK != REGISTER_GHCB_GPA_RESPONSE_INFO {
            bail!("Value is not a valid GHCP GPA registration response");
        }
        let ghcb_gpa = msr_value & GCHP_DATA_MASK;
        Ok(Self { ghcb_gpa })
    }
}

/// Registers the location of the GHCB page for the current vCPU with the hypervisor.
pub fn register_ghcb_location(request: RegisterGhcbGpaRequest) -> Result<()> {
    let request_ghcb_gpa: u64 = request.ghcb_gpa;
    write_msr_and_exit(request.into());
    let response: RegisterGhcbGpaResponse = read_msr().try_into()?;
    // Ensure that the registration was successful.
    if response.ghcb_gpa == GHCB_LOCATION_NOT_ACCEPTED {
        bail!("GHCB location registration not accepted");
    }
    if response.ghcb_gpa != request_ghcb_gpa {
        bail!("The registration response did not match the request");
    }
    Ok(())
}

/// Whether a memory page is private to the guest, or shared with the hypervisor.
#[derive(Debug, FromRepr)]
#[repr(u8)]
pub enum PageAssignment {
    Private = 1,
    Shared = 2,
}

/// Request to change a memory page from shared to private or private to shared.
pub struct SnpPageStateChangeRequest {
    page_gpa: u64,
    assignment: PageAssignment,
}

impl SnpPageStateChangeRequest {
    pub fn new(page_gpa: usize, assignment: PageAssignment) -> Result<Self> {
        let page_gpa = page_gpa as u64;
        if page_gpa & GHCB_INFO_MASK != 0 {
            bail!("Page must be 4KiB-aligned");
        }
        // Only 52 bits can be use for an address.
        const ADDRESS_MAX: u64 = (1 << 52) - 1;
        if page_gpa > ADDRESS_MAX {
            bail!("Page address is too high");
        }
        Ok(Self {
            page_gpa,
            assignment,
        })
    }
}

impl From<SnpPageStateChangeRequest> for u64 {
    fn from(request: SnpPageStateChangeRequest) -> Self {
        let info = 0x014;
        let assignment = (request.assignment as u64) << 52;
        info | request.page_gpa | assignment
    }
}

/// The response containing the result of the SNP Page State Change operation.
pub struct SnpPageStateChangeResponse {
    /// The error code from the page state change operation.
    ///
    /// A value of 0 indicates success. Any non-zero value means that the state was not changed.
    error_code: u32,
}

impl TryFrom<u64> for SnpPageStateChangeResponse {
    type Error = anyhow::Error;
    fn try_from(msr_value: u64) -> Result<Self> {
        const SNP_PAGE_STATE_CHANGE_RESPONSE_INFO: u64 = 0x015;
        const RESERVED_MASK: u64 = 0xFFFFF000;
        if msr_value & GHCB_INFO_MASK != SNP_PAGE_STATE_CHANGE_RESPONSE_INFO
            || msr_value & RESERVED_MASK != 0
        {
            bail!("Value is not a valid SNP Page State Change response");
        }
        let error_code = (msr_value >> 32) as u32;
        Ok(Self { error_code })
    }
}

/// Requests a change of state for a page to be either private to the guest VM, or shared with the
/// hypervisor.
///
/// This is useful if the GHCB has not yet been established, for example if a page must be shared
/// with the hypervisor to establish the GHCB.
pub fn change_snp_page_state(request: SnpPageStateChangeRequest) -> Result<()> {
    write_msr_and_exit(request.into());
    let response: SnpPageStateChangeResponse = read_msr().try_into()?;
    // Ensure that the page state change was successful.
    if response.error_code != 0 {
        bail!(
            "Page state change failed with error code: {}",
            response.error_code
        );
    }
    Ok(())
}

/// A request for the hypervisor's supported features.
pub struct HypervisorFeatureSupportRequest;

impl From<HypervisorFeatureSupportRequest> for u64 {
    fn from(_request: HypervisorFeatureSupportRequest) -> Self {
        0x080
    }
}

bitflags! {
    /// Flags indicating which features are supported by the hypervisor.
    #[derive(Default)]
    pub struct HypervisorFeatureSupportResponse: u64 {
        /// AMD SEV-SNP is supported.
        const SEV_SNP = (1 << 0);
        /// The new AMD SEV-SNP feature for starting new Application Processors (APs) is supported.
        const AP_CREATION = (1 << 1);
        /// Restricted interrrupt injection is supported.
        const RESTRICTED_INJECTION = (1 << 2);
        /// Timer support is available if restricted interrupt injection is enabled.
        const RESTRICTED_INJECTION_TIMER = (1 << 3);
    }
}

impl TryFrom<u64> for HypervisorFeatureSupportResponse {
    type Error = anyhow::Error;
    fn try_from(msr_value: u64) -> Result<Self> {
        const HYPERVISOR_FEATURE_SUPPORT_RESPONSE_INFO: u64 = 0x081;
        if msr_value & GHCB_INFO_MASK != HYPERVISOR_FEATURE_SUPPORT_RESPONSE_INFO {
            bail!("Value is not a valid Hypervisor Feature Support response");
        }
        HypervisorFeatureSupportResponse::from_bits(msr_value >> 12)
            .ok_or_else(|| anyhow!("Invalid Hypervisor Feature Support bitmap"))
    }
}

/// Requests a bitmap specifying the features supported by the hypervisor.
pub fn get_hypervisor_feature_support() -> Result<HypervisorFeatureSupportResponse> {
    let request = HypervisorFeatureSupportRequest;
    write_msr_and_exit(request.into());
    read_msr().try_into()
}

/// The reason for requesting termination from the hypervisor.
#[derive(Debug)]
#[repr(u8)]
pub enum TerminationReason {
    /// Non-specific termination request.
    General = 0,
    /// The supported range for the GHCB protocol version does not match.
    GhcbProtocolVersion = 1,
    /// The SEV-SNP features supported by the hypervisor is not sufficient.
    SnpFeatureNotSupported = 2,
}

/// Request for the hypervisor to terminate the guest.
pub struct TerminationRequest {
    pub reason: TerminationReason,
}

impl From<TerminationRequest> for u64 {
    fn from(request: TerminationRequest) -> Self {
        let info = 0x100;
        // We use the default reason set (0x0), so don't set any value for bits 12-15.
        let reason = (request.reason as u64) << 16;
        info | reason
    }
}

/// Requests termination from the hypervisor.
pub fn request_termination(request: TerminationRequest) {
    write_msr_and_exit(request.into());
    // Go into a HALT loop, in case the hypervisor did not honor the termination request.
    loop {
        x86_64::instructions::hlt();
    }
}

/// Writes a value to the MSR and calls VMGEXIT to hand control to the hypervisor.
pub fn write_msr_and_exit(msr_value: u64) {
    // Safety: This operation is safe because this specific MSR is used only for communicating with
    // the hypervisor, and does not have any other side-effects within the guest.
    unsafe {
        Msr::new(MSR_IDENTIFIER).write(msr_value);
    }
    vmgexit();
}

/// Reads the value of the model-specific register.
///
/// This typically used to get the result of an operation when the hypervisor resumes the guest
/// following a call to VMGEGIT.
pub fn read_msr() -> u64 {
    // Safety: This operation is safe because this specific MSR is used only for communicating with
    // the hypervisor, and does not have any other side-effects within the guest.
    unsafe { Msr::new(MSR_IDENTIFIER).read() }
}
