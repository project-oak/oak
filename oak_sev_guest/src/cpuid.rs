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

//! This module contains structs that can be used to interpret the contents of
//! the CPUID page that is provisioned into the VM guest memory during SEV-SNP
//! startup.

use core::arch::x86_64::CpuidResult;

use zerocopy::FromBytes;

use crate::interrupts::MutableInterruptStackFrame;

/// The maximum number of CPUID functions that can be included in the page.
pub const CPUID_COUNT_MAX: usize = 64;
/// The size of the CPUID page.
pub const CPUID_PAGE_SIZE: usize = 4096;

/// The CPUID function result of an invocation for a specific leaf and subleaf.
///
/// See: Table 16 in <https://www.amd.com/system/files/TechDocs/56860.pdf>
#[repr(C)]
#[derive(Debug, FromBytes)]
pub struct CpuidFunction {
    /// The input values when CPUID was invoked.
    pub input: CpuidInput,
    /// The resulting register values when CPUID was invoked.
    pub output: CpuidOutput,
    _reserved: u64,
}

static_assertions::assert_eq_size!(CpuidFunction, [u8; 48]);

/// The required input valus for invoking CPUID.
#[repr(C)]
#[derive(Debug, FromBytes, PartialEq, Eq)]
pub struct CpuidInput {
    /// The input value of the EAX register, which represents the CPUID leaf.
    pub eax: u32,
    /// The input value of the ECX register, which represents the CPUID
    /// sub-leaf.
    pub ecx: u32,
    /// The input value of the XCR0 extended control register.
    ///
    /// Only required when a request for CPUID 0x0000_000D is made. Must be zero
    /// otherwise.
    pub xcr0: u64,
    /// The value of the IA32_XSS model-specific register.
    ///
    /// Only required when a request for CPUID 0x0000_000D is made and the guest
    /// supports the XSS MSR. Must be zero otherwise.
    pub xss: u64,
}

impl From<&mut MutableInterruptStackFrame> for CpuidInput {
    fn from(value: &mut MutableInterruptStackFrame) -> Self {
        let eax = value.rax as u32;
        let ecx = value.rcx as u32;
        // We only set the value of XCR0 for CPUID 0x0000_000D.
        // See table 6 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
        let xcr0 = if eax == 0xD { x86_64::registers::xcontrol::XCr0::read_raw() } else { 0 };
        // We ignore XSS for now and always set it to 0, as it is only relevant for
        // CPUID 0x0000_000D, if the guest supports the IA32_XSS MSR and the
        // guest uses XSAVES and XRSTORS.
        let xss = 0;

        Self { eax, ecx, xcr0, xss }
    }
}

/// The resulting register values after invoking CPUID.
#[repr(C)]
#[derive(Debug, FromBytes)]
pub struct CpuidOutput {
    /// The EAX register output from calling CPUID.
    pub eax: u32,
    /// The EBX register output from calling CPUID.
    pub ebx: u32,
    /// The ECX register output from calling CPUID.
    pub ecx: u32,
    /// The EDX register output from calling CPUID.
    pub edx: u32,
}

impl From<CpuidOutput> for CpuidResult {
    fn from(value: CpuidOutput) -> Self {
        CpuidResult { eax: value.eax, ebx: value.ebx, ecx: value.ecx, edx: value.edx }
    }
}

/// Representation of the CPUID page.
///
/// See: Table 72 in <https://www.amd.com/system/files/TechDocs/56860.pdf>
#[repr(C, align(4096))]
#[derive(Debug, FromBytes)]
pub struct CpuidPage {
    /// The number of CPUID function results included in the page. Must not be
    /// greater than `CPUID_COUNT_MAX`.
    pub count: u32,
    /// Reserved. Must be 0.
    _reserved: [u8; 12],
    /// The CPUID function results.
    pub cpuid_data: [CpuidFunction; CPUID_COUNT_MAX],
}

static_assertions::assert_eq_size!(CpuidPage, [u8; CPUID_PAGE_SIZE]);

impl CpuidPage {
    /// Checks that the count is less than the maximum allowed count and that
    /// the reserved bytes are all zero.
    pub fn validate(&self) -> Result<(), &'static str> {
        if self.count as usize > CPUID_COUNT_MAX {
            return Err("invalid count");
        }
        if self._reserved.iter().any(|&value| value != 0) {
            return Err("nonzero value in _reserved");
        }
        Ok(())
    }
}
