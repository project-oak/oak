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
//! See section 2.3.1 in <https://developer.amd.com/wp-content/resources/56421.pdf> for more detail.

use crate::instructions::vmgexit;
use anyhow::{bail, Result};
use strum::FromRepr;
use x86_64::registers::model_specific::Msr;

/// The version of the GHCB MSR protocol supported by this library. This represents the version
/// specific to AMD SEV-SNP.
pub const SUPPORTED_PROTOCOL_VERION: u16 = 2;

/// The identifier for the MSR used in the protocol.
const MSR_IDENTIFIER: u32 = 0xC001_0130;

/// Mask to extract the GHCB info from a u64 value.
const GHCB_INFO_MASK: u64 = 0xFFF;

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

/// Sets the address of the GHCB page before exiting.
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
            bail!("Value is not a valid SEV information response.");
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
        let mut result = 0x004;
        result |= (request.leaf as u64) << 32;
        result |= (request.register as u64) << 30;
        result
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
            bail!("Value is not a valid CPUID response.");
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
