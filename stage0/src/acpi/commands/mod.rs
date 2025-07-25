//
// Copyright 2025 The Project Oak Authors
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

use sha2::Sha256;
use strum::FromRepr;

use crate::acpi::{files::Files, Firmware};

mod add_checksum;
mod add_pci_holes;
mod add_pci_root_stage1;
mod add_pci_root_stage2;
mod add_pointer;
mod allocate;
mod write_pointer;

pub const ROMFILE_LOADER_FILESZ: usize = 56;
pub type RomfileName = [u8; ROMFILE_LOADER_FILESZ];

pub use add_checksum::AddChecksum;
pub use add_pci_holes::AddPciHoles;
pub use add_pci_root_stage1::AddPciRootStage1;
pub use add_pci_root_stage2::AddPciRootStage2;
pub use add_pointer::AddPointer;
pub use allocate::Allocate;
pub use write_pointer::WritePointer;

#[repr(u32)]
#[derive(Debug, Eq, FromRepr, Ord, PartialEq, PartialOrd)]
pub enum CommandTag {
    Allocate = 1,
    AddPointer = 2,
    AddChecksum = 3,
    WritePointer = 4,

    // Extended VMM-specific commands
    AddPciHoles = 0x80000001,
    AddPciRootStage1 = 0x80000003,
    AddPciRootStage2 = 0x80000004,
}

impl CommandTag {
    /// VMM-specific commands that are not supported by QEMU should have the
    /// highest bit set.
    pub const VMM_SPECIFIC: u32 = 0x80000000;
}

pub trait Invoke<FW: Firmware, F: Files> {
    fn invoke(
        &self,
        files: &mut F,
        fwcfg: &mut FW,
        acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str>;
}

type Pad = [u8; 124];

#[repr(C)]
union Body {
    allocate: Allocate,
    pointer: AddPointer,
    checksum: AddChecksum,
    wr_pointer: WritePointer,
    pci_holes: AddPciHoles,
    pci_root_stage1: AddPciRootStage1,
    pci_root_stage2: AddPciRootStage2,
    padding: Pad,
}

impl Default for Body {
    fn default() -> Self {
        Body { padding: [Default::default(); 124] }
    }
}

impl PartialEq for Body {
    fn eq(&self, other: &Self) -> bool {
        // Compare raw bytes.
        // Safety: every byte sequence is valid as a u8 array.
        unsafe { self.padding == other.padding }
    }
}

#[repr(C)]
#[derive(Default, PartialEq)]
pub struct RomfileCommand {
    tag: u32,
    body: Body,
}

impl From<Allocate> for RomfileCommand {
    fn from(allocate: allocate::Allocate) -> Self {
        RomfileCommand { tag: CommandTag::Allocate as u32, body: Body { allocate } }
    }
}

impl From<AddPointer> for RomfileCommand {
    fn from(pointer: add_pointer::AddPointer) -> Self {
        RomfileCommand { tag: CommandTag::AddPointer as u32, body: Body { pointer } }
    }
}

impl From<AddChecksum> for RomfileCommand {
    fn from(checksum: add_checksum::AddChecksum) -> Self {
        RomfileCommand { tag: CommandTag::AddChecksum as u32, body: Body { checksum } }
    }
}

impl core::fmt::Debug for RomfileCommand {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // Safety: we check the tags; if a tag is not recognized, you get the padding
        // which accepts all values.
        f.debug_struct("RomfileCommand")
            .field("tag", &self.tag)
            .field(
                "body",
                match self.tag() {
                    Some(CommandTag::Allocate) => unsafe { &self.body.allocate },
                    Some(CommandTag::AddPointer) => unsafe { &self.body.pointer },
                    Some(CommandTag::AddChecksum) => unsafe { &self.body.checksum },
                    Some(CommandTag::WritePointer) => unsafe { &self.body.wr_pointer },
                    Some(CommandTag::AddPciHoles) => unsafe { &self.body.pci_holes },
                    Some(CommandTag::AddPciRootStage1) => unsafe { &self.body.pci_root_stage1 },
                    Some(CommandTag::AddPciRootStage2) => unsafe { &self.body.pci_root_stage2 },
                    _ => unsafe { &self.body.padding },
                },
            )
            .finish()
    }
}

impl RomfileCommand {
    fn tag(&self) -> Option<CommandTag> {
        CommandTag::from_repr(self.tag)
    }
}

impl<FW: Firmware, F: Files> Invoke<FW, F> for RomfileCommand {
    fn invoke(
        &self,
        files: &mut F,
        fwcfg: &mut FW,
        acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        if self.tag > CommandTag::VMM_SPECIFIC && self.tag().is_none() {
            log::warn!("ignoring proprietary ACPI linker command with tag {:#x}", self.tag);
            return Ok(());
        }
        if self.tag == 0 {
            // Safety: interpreting the union as a byte array is safe, as it makes no
            // assumptions about the meaning of any of the bytes.
            log::debug!("ignoring empty ACPI linker command with body {:?}", unsafe {
                &self.body.padding
            });
            return Ok(());
        }

        // Safety: we extract the value out of the union based on the tag value, which
        // is safe to do.
        let command: &dyn Invoke<FW, F> = match self.tag() {
            Some(CommandTag::Allocate) => unsafe { &self.body.allocate },
            Some(CommandTag::AddPointer) => unsafe { &self.body.pointer },
            Some(CommandTag::AddChecksum) => unsafe { &self.body.checksum },
            Some(CommandTag::WritePointer) => unsafe { &self.body.wr_pointer },
            Some(CommandTag::AddPciHoles) => unsafe { &self.body.pci_holes },
            Some(CommandTag::AddPciRootStage1) => unsafe { &self.body.pci_root_stage1 },
            Some(CommandTag::AddPciRootStage2) => unsafe { &self.body.pci_root_stage2 },
            _ => return Err("Invalid command tag in table-loader"),
        };
        command.invoke(files, fwcfg, acpi_digest)
    }
}
