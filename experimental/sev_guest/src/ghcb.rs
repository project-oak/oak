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

//! This module contains an implementation of the guest-host communications block (GHCB) page that
//! can be used for communicating with the hypervisor.

use zerocopy::FromBytes;

/// The size of the GHCB page.
pub const GHCB_PAGE_SIZE: usize = 4096;

/// The version of the GHCB protocol and page layout that the we expect to use.
pub const GHCB_PROTOCOL_VERSION: u16 = 2;

/// The guest-host communications block.
///
/// See: Table 3 in <https://developer.amd.com/wp-content/resources/56421.pdf>
#[repr(C, align(4096))]
#[derive(Debug, FromBytes)]
pub struct Ghcb {
    _reserved_0: [u8; 203],
    /// The current privilege level of the executing code.
    pub cpl: u8,
    _reserved_1: [u8; 116],
    /// The value of the IA32_XSS model-specific reqister.
    pub xss: u64,
    _reserved_2: [u8; 24],
    /// The value of the DR7 debug register.
    pub dr7: u64,
    _reserved_3: [u8; 144],
    /// The value of the RAX register.
    pub rax: u64,
    _reserved_4: [u8; 264],
    /// The value of the RBX register.
    pub rbx: u64,
    /// The value of the RCX register.
    pub rcx: u64,
    /// The value of the RDX register.
    pub rdx: u64,
    _reserved_5: [u8; 112],
    /// Guest-controlled exit code.
    pub sw_exit_code: u64,
    /// Guest-controlled exit information 1.
    pub sw_exit_info_1: u64,
    /// Guest-controlled exit information 2.
    pub sw_exit_info_2: u64,
    /// Guest-controlled additional information.
    pub sw_scratch: u64,
    _reserved_6: [u8; 56],
    /// Value of the XCR0 extended control register.
    pub xcr0: u64,
    /// Bitmap indicating which quadwords of the save state area are valid in the range from offset
    /// 0x000 through to offset 0x3ef.
    pub valid_bitmap: [u8; 16],
    /// The guest-physical address of the page that containing the x87-related saved state.
    pub x87_state_gpa: u64,
    _reserved_7: [u8; 1016],
    /// Area that can be used as a shared buffer for communicating additional information.
    pub shared_buffer: [u8; 2032],
    _reserved_8: [u8; 10],
    /// The version of the GHCB protocol and page layout in use.
    pub protocol_version: u16,
    /// The usage of the GHCB page. A value of 0 indicates the usage is in line with the definition
    /// as specified in this struct. Any other value indicates a hypervisor-defined usage.
    pub ghcb_usage: u32,
}

static_assertions::assert_eq_size!(Ghcb, [u8; GHCB_PAGE_SIZE]);
