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

//! Rust instruction wrappers for managing page state and interacting with the
//! hypervisor.

use core::arch::asm;

use bitflags::bitflags;
use strum::FromRepr;

/// Whether a page is in the validated state or not.
#[derive(Clone, Copy, Debug, FromRepr)]
#[repr(u32)]
pub enum Validation {
    /// The page is not validated.
    Unvalidated = 0,
    /// The page is validated.
    Validated = 1,
}

/// The size of a memory page.
#[derive(Clone, Copy, Debug, FromRepr)]
#[repr(u32)]
pub enum PageSize {
    /// The page is a 4KiB page.
    Page4KiB = 0,
    /// The page is a 2MiB page.
    Page2MiB = 1,
}

/// The potential errors when calling the PVALIDATE or RMPADJUST instructions.
#[derive(Debug, FromRepr, PartialEq)]
#[repr(u32)]
pub enum InstructionError {
    /// The input parameters were invalid.
    FailInput = 1,
    /// Insufficient permissions.
    FailPermission = 2,
    /// The page size does not match the page size entry in the RMP.
    FailSizeMismatch = 6,
    /// The page validation status was not updated. This value is software
    /// defined and will not be returned by the hardware instruction.
    ValidationStatusNotUpdated = 255,
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
    // Safety: this call does not modify the guest memory contents, so does not
    // violate memory safety.
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
            // If the carry flag is not 0, it indicates that the validated state was not
            // changed.
            Err(InstructionError::ValidationStatusNotUpdated)
        }
    } else {
        Err(InstructionError::from_repr(result)
            .expect("invalid return value from PVALIDATE instruction"))
    }
}

bitflags! {
    /// Permission mask used by the RMP.
    ///
    /// See Table 15-38 in <https://www.amd.com/system/files/TechDocs/24593.pdf> for more details.
    #[derive(Clone, Debug, PartialEq)]
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
#[derive(Debug, Clone, FromRepr, PartialEq)]
#[repr(u8)]
pub enum Vmsa {
    /// The page cannot be used as a VM save area.
    No = 0,
    /// The page can be used as a VM save area.
    Yes = 1,
}

/// Representation of the RMP permission used by the RMPADJUST instruction.
#[repr(C, align(8))]
#[derive(Debug, Clone, PartialEq)]
pub struct RmpPermission {
    /// The target VMPL to which the permission applies.
    pub target_vmpl: u8,
    /// The bit mask specifying the permission.
    pub perm_mask: PermissionMask,
    /// Whether this page can be used as a VM save area.
    pub vmsa: Vmsa,
    /// Padding to extend struct to 4 bytes in size.
    _reserved_0: u8,
    /// Padding to extend struct to 8 bytes in size to enable reinterpreting as
    /// a u64.
    _reserved_1: u32,
}

static_assertions::assert_eq_size!(RmpPermission, u64);

impl From<RmpPermission> for u64 {
    fn from(permission: RmpPermission) -> u64 {
        // Safety: reinterpreting the struct as a u64 is safe because the types are
        // guaranteed to have the same size and the struct is 8-byte aligned. We
        // are not making any assumptions about the individual bits.
        unsafe { core::mem::transmute(permission) }
    }
}

impl TryInto<RmpPermission> for u64 {
    type Error = &'static str;

    fn try_into(self) -> Result<RmpPermission, Self::Error> {
        let bytes = self.to_le_bytes();

        Ok(RmpPermission {
            target_vmpl: bytes[0],
            perm_mask: PermissionMask::from_bits(bytes[1])
                .ok_or("invalid permission mask value")?,
            vmsa: Vmsa::from_repr(bytes[2]).ok_or("invalid VMSA value")?,
            _reserved_0: bytes[3],
            _reserved_1: u32::from_le_bytes(bytes[4..].try_into().unwrap()),
        })
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
    // Safety: this call does not modify the guest memory contents, so does not
    // violate memory safety.
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
            .expect("invalid return value from RMPADJUST instruction"))
    }
}

/// Reads an RMP permission mask for a guest page.
///
/// See the RMPQUERY instruction in <https://www.amd.com/system/files/TechDocs/24594.pdf> for more details.
///
/// # Safety
///
/// If the page is not in `VALIDATED` state, calling this will cause an `#VC`
/// exception.
#[inline]
pub unsafe fn rmpquery(
    page_guest_physical_address: usize,
) -> Result<(RmpPermission, PageSize), InstructionError> {
    let permissions: u64;
    let page_size: u64;
    let result: u64;
    unsafe {
        asm!(
            // As the assembler doesn't recognize RMPQUERY (F3 0F 01 FD) yet, we use the REP (F3)
            // modifier on RDPRU (0F 01 FD) instruction to get the same result.
            "rep rdpru",
            in("rax") page_guest_physical_address,
            out("rdx") permissions,
            out("rcx") page_size,
            lateout("rax") result,
            options(nomem, nostack)
        );
    }

    if result == 0 {
        Ok((
            permissions.try_into().expect("invalid permissions bitmap"),
            PageSize::from_repr(page_size as u32)
                .expect("invalid page size value from RMPQUERY instruction"),
        ))
    } else {
        Err(InstructionError::from_repr(result as u32)
            .expect("invalid return value from RMPQUERY instruction"))
    }
}

/// Unconditionally exits from the guest to the hypervisor.
///
/// See the VMGEXIT instruction in <https://www.amd.com/system/files/TechDocs/24594.pdf> for more details.
pub fn vmgexit() {
    // Safety: this call does not modify the guest memory contents, so does not
    // violate memory safety.
    unsafe {
        // The REP instruction modifier changes the VMMCALL instruction to be equivalent
        // to the VMGEXIT call. This is used as the assembler does not recognise
        // the VMGEXIT mnemonic.
        asm!("rep vmmcall", options(nomem, nostack, preserves_flags));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rmp_permission_encdec() {
        let perms = RmpPermission {
            target_vmpl: 10,
            perm_mask: PermissionMask::all(),
            vmsa: Vmsa::Yes,
            _reserved_0: 123,
            _reserved_1: 456,
        };
        let perm_u64: u64 = perms.clone().into();
        let perms2: RmpPermission = perm_u64.try_into().unwrap();
        assert_eq!(perms, perms2);
    }
}
