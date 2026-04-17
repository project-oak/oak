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

use oak_sev_guest::io::{IoPortFactory, PortWriter};

use crate::hal::Port;

const PIC0_BASE: u16 = 0x20;
const PIC1_BASE: u16 = 0xA0;

pub struct Pic {
    command: Port<u8>,
    data: Port<u8>,
}

impl Pic {
    pub fn new<P: crate::Platform>(base: u16) -> Self {
        let factory = P::port_factory();
        Self { command: factory.new_writer(base), data: factory.new_writer(base + 1) }
    }

    pub unsafe fn write_command(&mut self, command: u8) -> Result<(), &'static str> {
        unsafe { self.command.try_write(command) }
    }

    pub unsafe fn write_data(&mut self, data: u8) -> Result<(), &'static str> {
        unsafe { self.data.try_write(data) }
    }

    pub unsafe fn init(
        &mut self,
        interrupt_offset: u8,
        chaining: u8,
        mask: u8,
    ) -> Result<(), &'static str> {
        // The initialization process is documented in https://wiki.osdev.org/8259_PIC
        // ICW1: ICW_INIT | ICW_ICW4
        unsafe { self.write_command(0x11) }?;
        // ICW2: the interrupt offset.
        unsafe { self.write_data(interrupt_offset) }?;
        // ICW3, chaining between PICs
        unsafe { self.write_data(chaining) }?;
        // ICW4, operation mode: ICW4_8086
        unsafe { self.write_data(0x01) }?;
        // OCW1: interrupt masking
        unsafe { self.write_data(mask) }?;
        Ok(())
    }
}

/// Initializes and disables the two legacy 8259 PICs in the system.
///
/// # Safety
///
/// The caller needs to guarantee that the PIC0 and PIC1 are at their well-known
/// I/O ports of 0x20 and 0xA0.
pub unsafe fn disable_pic8259<P: crate::Platform>() -> Result<(), &'static str> {
    let mut pic0 = Pic::new::<P>(PIC0_BASE);
    let mut pic1 = Pic::new::<P>(PIC1_BASE);

    // PIC0 interrupts will start at 0x20 (32), PIC1 at IRQ2, disable all interrupts
    unsafe { pic0.init(0x20, 4, 0xFF) }?;
    // PIC1 interrupts will start at 0x28 (40), cascade identity, and again disable
    // all interrupts
    unsafe { pic1.init(0x28, 2, 0xFF) }
}
