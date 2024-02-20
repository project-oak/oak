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

use oak_sev_snp_guest::io::{IoPortFactory, PortWrapper, PortWriter};

use crate::io_port_factory;

const PIC0_BASE: u16 = 0x20;
const PIC1_BASE: u16 = 0xA0;

pub struct Pic {
    command: PortWrapper<u8>,
    data: PortWrapper<u8>,
}

impl Pic {
    pub fn new(base: u16) -> Self {
        Self {
            command: io_port_factory().new_writer(base),
            data: io_port_factory().new_writer(base + 1),
        }
    }

    pub unsafe fn write_command(&mut self, command: u8) -> Result<(), &'static str> {
        self.command.try_write(command)
    }

    pub unsafe fn write_data(&mut self, data: u8) -> Result<(), &'static str> {
        self.data.try_write(data)
    }

    pub unsafe fn init(
        &mut self,
        interrupt_offset: u8,
        chaining: u8,
        mask: u8,
    ) -> Result<(), &'static str> {
        // The initialization process is documented in https://wiki.osdev.org/8259_PIC
        // ICW1: ICW_INIT | ICW_ICW4
        self.write_command(0x11)?;
        // ICW2: the interrupt offset.
        self.write_data(interrupt_offset)?;
        // ICW3, chaining between PICs
        self.write_data(chaining)?;
        // ICW4, operation mode: ICW4_8086
        self.write_data(0x01)?;
        // OCW1: interrupt masking
        self.write_data(mask)?;
        Ok(())
    }
}

/// Initializes and disables the two legacy 8259 PICs in the system.
///
/// # Safety
///
/// The caller needs to guarantee that the PIC0 and PIC1 are at their well-known I/O ports of 0x20
/// and 0xA0.
pub unsafe fn disable_pic8259() -> Result<(), &'static str> {
    let mut pic0 = Pic::new(PIC0_BASE);
    let mut pic1 = Pic::new(PIC1_BASE);

    // PIC0 interrupts will start at 0x20 (32), PIC1 at IRQ2, disable all interrupts
    pic0.init(0x20, 4, 0xFF)?;
    // PIC1 interrupts will start at 0x28 (40), cascade identity, and again disable all interrupts
    pic1.init(0x28, 2, 0xFF)
}
