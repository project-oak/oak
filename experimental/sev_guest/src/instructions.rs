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

//! Rust instruction wrappers for managing page state and interacting with the hypervisor.

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

/// The potential errors when calling the PVALIDATE or RMPADJUST instructions.
#[derive(Debug, FromRepr)]
#[repr(u32)]
pub enum InstructionError {
    /// The input parameters were invalid.
    FailInput = 1,
    /// Insufficient permissions.
    FailPermission = 2,
    /// The page size does not match the page size entry in the RMP.
    FailSizeMismatch = 6,
    /// The page validation status was not updated. This value is software defined and will not be
    /// returned by the hardware instruction.
    ValdationStatusNotUpdated = 255,
}

/// Marks a page as validated or unvalidated in the RMP.
///
/// See the PVALIDATE instruction in <https://www.amd.com/system/files/TechDocs/24594.pdf> for more details.
#[inline]
pub fn pvalidate(
    page_guest_physical_address: usize,
    page_size: PageSize,
    validated: Validation,
) -> Result<(), InstructionError> {
    let page_size = page_size as u32;
    let validated = validated as u32;
    let result: u32;
    let carry: u8;
    // Safety: this call does not modify the guest memory contents, so does not violate memory
    // safety.
    unsafe {
        asm!(
            "pvalidate",
            "setc dl",
            in("rax") page_guest_physical_address,
            in("ecx") page_size,
            in("edx") validated,
            lateout("eax") result,
            lateout("dl") carry,
            options(nomem, nostack)
        );
    }
    if result == 0 {
        if carry == 0 {
            Ok(())
        } else {
            // If the carry flag is not 0, it indicates that the validated state was not changed.
            Err(InstructionError::ValdationStatusNotUpdated)
        }
    } else {
        Err(InstructionError::from_repr(result)
            .expect("Invalid return value from PVALIDATE instruction."))
    }
}

bitflags! {
    /// Permission mask used by the RMP.
    ///
    /// See Table 15-38 in <https://www.amd.com/system/files/TechDocs/24593.pdf> for more details.
    pub struct PermissionMask: u8 {
        /// The target VMPL can read the page.
        const READ = 1;
        /// The target VMPL can write to the page.
        const WRITE = 2;
        /// Code in the page can be executed in ring 3.
        const EXECUTE_USER = 4;
        /// Code in the page can be executed in rings 0..2.
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

/// Representation of the RMP permission used by the RMPADJUST instruction.
#[repr(C, align(8))]
pub struct RmpPermission {
    /// The target VMPL to which the permission applies.
    pub target_vmpl: u8,
    /// The bit mask specifying the permission.
    pub perm_mask: PermissionMask,
    /// Whether this page can be used as a VM save area.
    pub vmsa: Vmsa,
    /// Padding to extend struct to 4 bytes in size.
    _reserved_0: u8,
    /// Padding to extend struct to 8 bytes in size to enable reinterpreting as a u64.
    _reserved_1: u32,
}

static_assertions::assert_eq_size!(RmpPermission, u64);

impl From<RmpPermission> for u64 {
    fn from(permission: RmpPermission) -> u64 {
        // Safety: reinterpreting the struct as a u64 is safe because the types are guaranteed to
        // have the same size and the struct is 8-byte aligned. We are not making any assumptions
        // about the individual bits.
        unsafe { core::mem::transmute(permission) }
    }
}

/// Adjusts the permissions of a page in the RMP.
///
/// See the RMPADJUST instruction in <https://www.amd.com/system/files/TechDocs/24594.pdf> for more details.
#[inline]
pub fn rmpadjust(
    page_guest_physical_address: usize,
    page_size: PageSize,
    permission: RmpPermission,
) -> Result<(), InstructionError> {
    let page_size = page_size as u64;
    let permission: u64 = permission.into();
    let result: u64;
    // Safety: this call does not modify the guest memory contents, so does not violate memory
    // safety.
    unsafe {
        asm!(
            "rmpadjust",
            in("rax") page_guest_physical_address,
            in("rcx") page_size,
            in("rdx") permission,
            lateout("rax") result,
            options(nomem, nostack)
        );
    }
    if result == 0 {
        Ok(())
    } else {
        Err(InstructionError::from_repr(result as u32)
            .expect("Invalid return value from RMPADJUST instruction."))
    }
}

/// Unconditionally exits from the guest to the hypervisor.
///
/// See the VMGEXIT instruction in <https://www.amd.com/system/files/TechDocs/24594.pdf> for more details.
pub fn vmgexit() {
    // Safety: this call does not modify the guest memory contents, so does not violate memory
    // safety.
    unsafe {
        // The REP instruction modifier changes the VMMCALL instruction to be equivalent to the
        // VMGEXIT call. This is used as the assembler does not recognise the VMGEXIT mnemonic.
        asm!("rep vmmcall", options(nomem, nostack, preserves_flags));
    }
}
