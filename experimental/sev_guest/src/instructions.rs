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

//! Rust instruction wrappers managing page state and interacting with the hypervisor.

use bitflags::bitflags;
use core::arch::asm;
use strum::FromRepr;

/// Whether a page is in the validated state or not.
#[derive(Debug, FromRepr)]
#[repr(u32)]
pub enum Validation {
    /// The page is not validated.
    Unvalidated = 0,
    /// The page is validated.
    Validated = 1,
}

/// The size of a memory page.
#[derive(Debug, FromRepr)]
#[repr(u32)]
pub enum PageSize {
    /// The page is a 4KiB page.
    Page4KiB = 0,
    /// The page is a 2MiB page.
    Page2MiB = 1,
}

/// The result from calling the PVALIDATE or RMPADJUST instructions.
#[derive(Debug, FromRepr)]
#[repr(u32)]
pub enum InstructionResult {
    /// The operation was successful.
    Success = 0,
    /// The input parameters were invalid.
    FailInput = 1,
    /// Insufficient permissions.
    FailPermission = 2,
    /// The page size does not match the page size entry in the RMP.
    FailSizeMismatch = 6,
}

/// Marks a page as validated or unvalidated in the RMP.
///
/// See the PVALIDATE instruction in <https://www.amd.com/system/files/TechDocs/24594.pdf> for more details.
#[inline]
pub fn pvalidate(page_addr: u64, page_size: PageSize, validated: Validation) -> InstructionResult {
    let page_size = page_size as u32;
    let validated = validated as u32;
    let result: u32;
    // Safety: this call does not modify the guest memory contents, so does not violate memory
    // safety.
    unsafe {
        asm!(
            "pvalidate",
            in("rax") page_addr,
            in("ecx") page_size,
            in("edx") validated,
            lateout("eax") result,
            options(nomem, nostack)
        );
    }
    InstructionResult::from_repr(result).expect("Invalid result from PVALIDATE instruction")
}

bitflags! {
    /// Permission mask used by the RMP.
    ///
    /// See the RMPADJUST instruction in <https://www.amd.com/system/files/TechDocs/24594.pdf> for more details.
    pub struct PermissionMask: u8 {
        /// The target VMPL can read the page.
        const READ = 1;
        /// The target VMPL can write to the page.
        const WRITE = 2;
        /// Code in the page can be executed at CPL3.
        const EXECUTE_USER = 4;
        /// Code in the page can be executed at CPL0..2
        const EXECUTE_SUPERVISOR = 8;
    }
}

/// Whether the page can be used as a VM save area.
#[derive(Debug, FromRepr)]
#[repr(u8)]
pub enum Vmsa {
    /// The page cannot be used as a VM save area.
    No = 0,
    /// The page can be used as a VM save area.
    Yes = 1,
}

/// Representation of the RMP permission used by the RMPADJST instruction.
pub struct RmpPermission {
    /// The target VMPL to which the permission applies.
    target_vmpl: u8,
    /// The bit mask specifying the permission.
    perm_mask: PermissionMask,
    /// Whether this page can be used as a VM save area.
    vmsa: Vmsa,
}

impl From<RmpPermission> for u64 {
    fn from(permission: RmpPermission) -> u64 {
        let mut buffer = [0u8; 8];
        buffer[0] = permission.target_vmpl;
        buffer[1] = permission.perm_mask.bits;
        buffer[2] = permission.vmsa as u8;
        u64::from_be_bytes(buffer)
    }
}

/// Adjusts the permissions of a page in the RMP.
///
/// See the RMPADJUST instruction in <https://www.amd.com/system/files/TechDocs/24594.pdf> for more details.
#[inline]
pub fn rmpadjust(
    page_addr: u64,
    page_size: PageSize,
    permission: RmpPermission,
) -> InstructionResult {
    let page_size = page_size as u64;
    let permission: u64 = permission.into();
    let result: u64;
    // Safety: this call does not modify the guest memory contents, so does not violate memory
    // safety.
    unsafe {
        asm!(
            "rmpadjust",
            in("rax") page_addr,
            in("rcx") page_size,
            in("rdx") permission,
            lateout("rax") result,
            options(nomem, nostack)
        );
    }
    InstructionResult::from_repr(result as u32).expect("Invalid result from RMPADJUST instruction")
}

/// Unconditionally exits from the guest to the hypervisor.
///
/// See the VMGEXIT instruction in <https://www.amd.com/system/files/TechDocs/24594.pdf> for more details.
pub fn vmgexit() {
    // Safety: this call does not modify the guest memory contents, so does not violate memory
    // safety.
    unsafe {
        // The REP instruction modifier changes the VMMCALL instruction to be equivalent to the
        // VMGEXIT call. this is used as the assembler does not recognise the VMGEXIT mnemonic.
        asm!("rep vmmcall", options(nomem, nostack, preserves_flags));
    }
}
