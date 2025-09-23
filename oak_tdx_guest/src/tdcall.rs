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

//! Rust implementation of the TDX TDCALL instruction.

use core::{arch::asm, mem::size_of};

use bitflags::bitflags;
use strum::{Display, FromRepr};
use x86_64::structures::paging::{PageSize, PhysFrame, Size2MiB, Size4KiB};

/// The result from an instruction that indicates success.
const SUCCESS: u64 = 0;

bitflags! {
    /// Attributes of a TD.
    ///
    /// See section 3.4.1 of [Intel® Trust Domain Extensions (Intel® TDX) Module
    /// Architecture Application Binary Interface (ABI) Reference Specification]
    /// (https://cdrdv2.intel.com/v1/dl/getContent/733579) Draft 1.5.05.44 for
    /// more information.
    #[derive(Default)]
    pub struct Attributes: u64 {
        /// The guest TD runs in off-TD debug mode.
        ///
        /// If this is enabled the TD should be considered untrusted.
        const DEBUG = 1 << 0;
        /// The TD participates in HGS+ operation. HGS+ monitors the TD
        /// operation as part of the whole system.
        /// This bit may be set, if supported by the TDX module, regardless
        /// on CPU support.
        const HGS_PLUS_PROF = 1 << 4;
        /// The TD participates in system profiling using performance monitoring
        /// counters. Those counters are not context-switched on TD entry and
        /// exit; they monitor the TD operation as part of the whole system.
        /// This bit may be set, if supported by the TDX module, regardless on
        /// CPU support.
        const PERF_PROF = 1 << 5;
        /// The TD participates in system profiling using core out-of-band
        /// telemetry. Core telemetry monitors the TD operation as part of the
        /// whole system.
        /// This bit may be set, if supported by the TDX module, regardless of
        /// CPU support.
        const PMT_PROF = 1 << 6;
        /// TD is allowed to use Linear Address Space Separation.
        /// This bit may only be set if both the TDX module and the CPU support
        /// LASS.
        const LASS = 1 << 27;
        /// Disable EPT violation conversion to #VE on guest TD access of
        /// PENDING pages
        const SEPT_VE_DISABLE = 1 << 28;
        /// Whether the TD is migratable
        const MIGRATABLE = 1 << 29;
        /// Whether the TD is allowed to use Supervisor Protection Keys.
        const PKS = 1 << 30;
        /// Whether the TD is allowed to use Key Locker.
        ///
        /// Must be 0 for the current version.
        const KL = 1 << 31;
        /// The TD is a TDX Connect Provisioning Agent.
        /// This bit may only be set if both the TDX module and the CPU support
        /// TDX Connect.
        const TPA = 1 << 62;
        /// Whether the TD is allowed to use Perfmon and PERF_METRICS.
        const PERFMON = 1 << 63;
    }
}

/// Information about the TD's execution environment.
///
/// See section 2.4.2 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://www.intel.com/content/dam/develop/external/us/en/documents/intel-tdx-guest-hypervisor-communication-interface.pdf)
/// for more information.
pub struct TdInfo {
    /// The effective GPA width. The "shared" bit is at position gpa_width - 1.
    ///
    /// Currently only values of 48 or 52 are possible.
    pub gpa_width: usize,
    /// The TD attributes passed as part of TDINIT.
    pub attributes: Attributes,
    /// The number of vCPUs enabled on this TD.
    pub num_vcpus: u32,
    /// The maximum possible number of vCPUs for this TD.
    pub max_vcpus: u32,
}

/// Gets information about the TD's execution environment by calling the
/// TDCALL[TDG.VP.INFO] leaf.
///
/// See section 2.4.2 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://www.intel.com/content/dam/develop/external/us/en/documents/intel-tdx-guest-hypervisor-communication-interface.pdf)
/// for more information.
pub fn get_td_info() -> TdInfo {
    // The TDCALL leaf for TDG.VP.INFO.
    const LEAF: u64 = 1;

    let mut result: i64;
    let mut gpa_width: usize;
    let mut attributes: u64;
    let mut vcpu_info: u64;
    // The TDCALL leaf goes into RAX. RAX returns the result (0 is success). RCX
    // returns the GPA width in the first 6 bits. RDX returns the TD attributes.
    // R8 contains the number of active or ready vCPUs in bits 0..32 and the
    // maximum number of vCPUs in bits 32..64. R9, R10 and R11 are reserved for
    // future use. We zero out all output registers in the input to make sure old
    // register values don't accidentally leak to the hypervisor.
    //
    // Safety: calling TDCALL here is safe since it does not alter memory and all
    // the affected registers are specified, so no unspecified registers will be
    // clobbered.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") LEAF => result,
            inout("rcx") 0u64 => gpa_width,
            inout("rdx") 0u64 => attributes,
            inout("r8") 0u64 => vcpu_info,
            inout("r9") 0u64 => _,
            inout("r10") 0u64 => _,
            inout("r11") 0u64 => _,

            options(nomem, nostack),
        );
    }
    // According to the spec this instruction will always return 0 in RAX.
    assert_eq!(result, SUCCESS as i64, "TDCALL[TDG.VP.INFO] returned an invalid result");
    let attributes = Attributes::from_bits(attributes).expect("invalid TD attributes");
    let (num_vcpus, max_vcpus) = split_u64(vcpu_info);
    TdInfo { gpa_width, attributes, num_vcpus, max_vcpus }
}

/// Information about a virtualization exception (#VE).
///
/// See section 2.4.4 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://www.intel.com/content/dam/develop/external/us/en/documents/intel-tdx-guest-hypervisor-communication-interface.pdf)
/// for more information.
pub struct VeInfo {
    /// The exit reason.
    pub exit_reason: u32,
    /// The exit qualification.
    pub exit_qualification: u64,
    /// The guest-linear address (virtual address).
    pub guest_linear_address: u64,
    /// The guest-physical address.
    pub guest_physical_address: u64,
    /// The length of the instruction that caused the #VE.
    pub instruction_length: u32,
    /// Additional context for the instruction that caused the #VE.
    pub instruction_info: u32,
}

/// Gets information about the recent virtualization exception (#VE) by calling
/// the TDCALL[TDG.VP.VEINFO.GET] leaf.
///
/// See section 2.4.4 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)]( https://www.intel.com/content/dam/develop/external/us/en/documents/intel-tdx-guest-hypervisor-communication-interface.pdf)
/// for more information.
pub fn get_ve_info() -> Option<VeInfo> {
    // The TDCALL leaf for TDG.VP.VEINFO.GET.
    const LEAF: u64 = 3;
    // The result if there were no recent #VE exepctions.
    const NO_VE_INFO: u64 = 1 << 63;

    let mut result: u64;
    let mut exit_reason: u64;
    let mut exit_qualification: u64;
    let mut guest_linear_address: u64;
    let mut guest_physical_address: u64;
    let mut instruction: u64;

    // The TDCALL leaf goes into RAX. RAX returns the result (0 is success). RCX
    // returns the exit reason. RDX returns the exit qualification. R8 returns
    // the guest-linear address. R9 returns the guest-physical address. R10
    // returns the instructions length in bits 0..32 and the additional
    // instruction info in bits 32..64. We zero out all output registers in the
    // input to make sure old register values don't accidentally leak to the
    // hypervisor.
    //
    // Safety: calling TDCALL here is safe since it does not alter memory and all
    // the affected registers are specified, so no unspecified registers will be
    // clobbered.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") LEAF => result,
            inout("rcx") 0u64 => exit_reason,
            inout("rdx") 0u64 => exit_qualification,
            inout("r8") 0u64 => guest_linear_address,
            inout("r9") 0u64 => guest_physical_address,
            inout("r10") 0u64 => instruction,

            options(nomem, nostack),
        );
    }

    if result == NO_VE_INFO {
        // No recent #VE.
        return None;
    }
    // According to the spec this instruction will always return either 0 or
    // NO_VE_INFO in RAX.
    assert_eq!(result, SUCCESS, "TDCALL[TDG.VP.VEINFO.GET] returned an invalid result");

    let exit_reason: u32 = exit_reason.try_into().expect("invalid exit reason");
    let (instruction_length, instruction_info) = split_u64(instruction);

    Some(VeInfo {
        exit_reason,
        exit_qualification,
        guest_linear_address,
        guest_physical_address,
        instruction_length,
        instruction_info,
    })
}

/// Error when accepting guest-physical memory.
#[derive(Debug, Display, FromRepr)]
#[repr(u64)]
pub enum AcceptMemoryError {
    /// The supplied operand in Rcx is invalid.
    InvalidOperandInRcx = 0xC000010000000001,
    /// Operation encountered a busy operand, indicated by the lower 32 bits of
    /// the status. In many cases, this can be resolved by retrying the
    /// operation. Specifically, it may indicate that a concurrent
    /// TDG.MEM.PAGE.ACCEPT is using the same Secure EPT entry
    OperandBusy = 0x8000020000000000,
    /// The page is not pending and has already been accepted.
    AlreadyAccepted = 0x00000B0A00000000,
    /// Requested page size is 2MB, but the page GPA is not mapped at 2MB size
    /// Note it ends with 0x1 which means the operand is RCX
    PageSizeMisMatch = 0xC0000B0B00000001, //rcx
}

#[derive(Debug)]
#[repr(u64)]
pub enum TdxPageSize {
    Size4KiB = 0,
    Size2MiB = 1,
}

/// Trait for getting the associated `TdxPageSize` enum for a memory page of the
/// given size.
pub trait TdxSize {
    fn tdx_size() -> TdxPageSize;
}

impl TdxSize for Size4KiB {
    fn tdx_size() -> TdxPageSize {
        TdxPageSize::Size4KiB
    }
}

impl TdxSize for Size2MiB {
    fn tdx_size() -> TdxPageSize {
        TdxPageSize::Size2MiB
    }
}

/// Accepts a pending private memory page to make it usable in the guest, by
/// calling the TDCALL [TDG.MEM.PAGE.ACCEPT] leaf.
///
/// This call also zeros the memory in the page.
///
/// See section 2.4.7 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://www.intel.com/content/dam/develop/external/us/en/documents/intel-tdx-guest-hypervisor-communication-interface.pdf)
/// for more information.
pub fn accept_memory<S: PageSize + TdxSize>(frame: PhysFrame<S>) -> Result<(), AcceptMemoryError> {
    // The TDCALL leaf for TDG.MEM.PAGE.ACCEPT.
    const LEAF: u64 = 6;

    let mut result: u64;
    let gpa = frame.start_address().as_u64();
    let page_size = S::tdx_size() as u64;

    // The TDCALL leaf goes into RAX. RAX returns the result (0 is success). The
    // guest-physical address of the start of the memory page goes into [51:12]
    // of RCX. The page size goes to [2:0] of RCX. 0 for 4KiB, 1 for 2MiB.
    //
    // Safety: calling TDCALL here is safe since it does not alter memory and all
    // the affected registers are specified, so no unspecified registers will be
    // clobbered. The newly added page cannot be a previously accepted page, so
    // it will not affect memory that is already in use.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") LEAF => result,
            in("rcx") gpa | page_size,
            options(nomem, nostack),
        );
    }

    if result > 0 {
        // According to the spec the result will either be 0 (Success) or one of the
        // defined error values.
        return Err(AcceptMemoryError::from_repr(result)
            .expect("TDCALL[TDG.MEM.PAGE.ACCEPT] returned an invalid result"));
    }

    Ok(())
}

/// The index of a run-time measurement register (RTMR).
#[derive(Debug)]
#[repr(u64)]
pub enum RtmrIndex {
    Rtmr0 = 0,
    Rtmr1 = 1,
    Rtmr2 = 2,
    Rtmr3 = 3,
}

/// A buffer that can be used for extending an RTMR.
///
/// It must be 64-byte aligned and have a length of 48 bytes.
#[repr(C, align(64))]
pub struct ExtensionBuffer {
    pub data: [u8; 48],
}

/// Error when extending an RTMR.
///
/// These values are derived from the TDX Function Completion status structure.
/// See section 3.1.1 of the [Intel® TDX Module v1.5 ABI Specification](https://cdrdv2.intel.com/v1/dl/getContent/817877?fileName=intel-tdx-module-1.5-abi-spec-348551004.pdf)
/// for more information.
#[derive(Debug, Display, FromRepr)]
#[repr(u64)]
pub enum ExtendRtmrError {
    /// The supplied operand is invalid.
    InvalidOperand = 0xC000010000000000,
    /// Operation encountered a busy operand, indicated by the lower 32 bits of
    /// the status. In many cases, this can be resolved by retrying the
    /// operation.
    OperandBusy = 0x8000020000000000,
}

/// Extends the specified run-time measurement register (RTMR) with the given
/// data.
///
/// See section 5.4.6 of the [Intel® TDX Module v1.5 ABI Specification](https://cdrdv2.intel.com/v1/dl/getContent/817877?fileName=intel-tdx-module-1.5-abi-spec-348551004.pdf)
/// for more information.
pub fn extend_rtmr(rtmr_index: RtmrIndex, buf: &ExtensionBuffer) -> Result<(), ExtendRtmrError> {
    // The TDCALL leaf for TDG.MR.RTMR.EXTEND.
    const LEAF: u64 = 2;

    let mut result: u64;
    let buf_gpa = buf.data.as_ptr() as usize as u64;
    let rtmr_index = rtmr_index as u64;

    // The TDCALL leaf goes into RAX. RAX returns the result (0 is success). The
    // guest-physical address of the start of the extension buffer goes into RCX.
    // The RTMR index goes into RDX.
    //
    // Safety: calling TDCALL here is safe since it does not alter memory and all
    // the affected registers are specified, so no unspecified registers will be
    // clobbered.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") LEAF => result,
            in("rcx") buf_gpa,
            in("rdx") rtmr_index,
            options(nomem, nostack),
        );
    }

    if result > 0 {
        // According to the spec the result will either be 0 (Success) or one of the
        // defined error values. The lower 32 bits can contain additional information
        // that we ignore for now.
        return Err(ExtendRtmrError::from_repr(result & 0xFFFFFFFF00000000)
            .expect("TDCALL[TDG.MR.RTMR.EXTEND] returned an invalid result"));
    }

    Ok(())
}

/// Splits a 64-bit little-endian unsigned integer into two 32-bit little-endian
/// unsigned integers.
///
/// The first value represents the lower 32-bits and the second the higher bits.
fn split_u64(value: u64) -> (u32, u32) {
    const SIZE: usize = size_of::<u32>();
    let bytes = value.to_le_bytes();
    let (lower, higher) = bytes.split_array_ref::<SIZE>();
    (u32::from_le_bytes(*lower), u32::from_le_bytes(higher.try_into().unwrap()))
}
