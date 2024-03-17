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

#[repr(C)]
pub struct ApResetAddress {
    // IP register value where to jump
    reset_ip: u16,

    // CS register value where to jump
    reset_cs: u16,
}
static_assertions::assert_eq_size!(ApResetAddress, [u8; 4]);

/// AP Jump Table.
///
/// See: Section 4.3.1.1 in <https://www.amd.com/content/dam/amd/en/documents/epyc-technical-docs/specifications/56421-guest-hypervisor-communication-block-standardization.pdf>
#[repr(C, align(4096))]
pub struct ApJumpTable {
    /// Reset address where the AP should jump when handing over control to the
    /// OS.
    reset_address: ApResetAddress,
    _padding: [u8; 4092],
}
static_assertions::assert_eq_size!(ApJumpTable, [u8; 4096]);
