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

//! This module contains structs that can be used to interpret the contents of the CPUID page that
//! is provisioned into the VM guest memory during SEV-SNP startup.

use zerocopy::FromBytes;

/// The maximum number of CPUID functions that can be included in the page.
pub const CPUID_COUNT_MAX: usize = 64;
/// The size of the CPUID page.
pub const CPUID_PAGE_SIZE: usize = 4096;

/// The CPUID function result of an invocation for a specific leaf and subleaf.
///
/// See: Table 14 in <https://www.amd.com/system/files/TechDocs/56860.pdf>
#[repr(C)]
#[derive(Debug, FromBytes)]
pub struct CpuidFunction {
    /// The input value of the EAX register when CPUID was called. This represents the CPUID leaf.
    pub eax_in: u32,
    /// The input value of the ECX register when CPUID was called. This represents the CPUID
    /// sub-leaf.
    pub ecx_in: u32,
    /// The value of the XCR0 extended control register when CPUID was called.
    pub xcr0_in: u64,
    /// The value of the IA32_XSS model-specific register when CPUID was called.
    pub xss_in: u64,
    /// The EAX register output from calling CPUID.
    pub eax: u32,
    /// The EBX register output from calling CPUID.
    pub ebx: u32,
    /// The ECX register output from calling CPUID.
    pub ecx: u32,
    /// The EDX register output from calling CPUID.
    pub edx: u32,
    _reserved: u64,
}

/// Representation of the CPUID page.
///
/// See: Table 69 in <https://www.amd.com/system/files/TechDocs/56860.pdf>
#[repr(C, align(4096))]
#[derive(Debug, FromBytes)]
pub struct CpuidPage {
    /// The number of CPUID function results included in the page. Must not be greated than
    /// `CPUID_COUNT_MAX`.
    pub count: u32,
    _reserved: [u8; 12],
    /// The CPUID function results.
    pub cpuid_data: [CpuidFunction; CPUID_COUNT_MAX],
}

static_assertions::assert_eq_size!(CpuidPage, [u8; CPUID_PAGE_SIZE]);
