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

use oak_sev_guest::io::{IoPortFactory, PortReader, PortWrapper, PortWriter};

use crate::io_port_factory;

const CMOS_INDEX_PORT: u16 = 0x0070;
const CMOS_DATA_PORT: u16 = 0x0071;

// QEMU-specific CMOS config fields.
const CMOS_MEM_EXTMEM_LOW: u8 = 0x30;
const CMOS_MEM_EXTMEM_HIGH: u8 = 0x31;
const CMOS_MEM_EXTMEM2_LOW: u8 = 0x34;
const CMOS_MEM_EXTMEM2_HIGH: u8 = 0x35;
const CMOS_MEM_HIGHMEM_LOW: u8 = 0x5b;
const CMOS_MEM_HIGHMEM_MID: u8 = 0x5c;
const CMOS_MEM_HIGHMEM_HIGH: u8 = 0x5d;

const NMI_DISABLE_BIT: u8 = 0x80;

pub struct Cmos {
    index_port: PortWrapper<u8>,
    data_port: PortWrapper<u8>,
}

impl Cmos {
    /// Creates a new CMOS reader wrapper.
    ///
    /// # Safety
    ///
    /// It's up to the caller to guarantee that there will be no other readers/writers to the CMOS
    /// ports (0x70, 0x71) and that CMOS is actually available on those ports, otherwise the
    /// behaviour is undefined.
    pub unsafe fn new() -> Self {
        Self {
            index_port: io_port_factory().new_writer(CMOS_INDEX_PORT),
            data_port: io_port_factory().new_reader(CMOS_DATA_PORT),
        }
    }

    /// Returns the low RAM size (memory under the 4 GiB mark)
    pub fn low_ram_size(&mut self) -> Result<u32, &'static str> {
        let mut rs: u32 = (self.read(CMOS_MEM_EXTMEM2_LOW)? as u32) << 16;
        rs |= (self.read(CMOS_MEM_EXTMEM2_HIGH)? as u32) << 24;

        if rs > 0 {
            rs += 16 * 1024 * 1024; // 16 MiB
        } else {
            rs = (self.read(CMOS_MEM_EXTMEM_LOW)? as u32) << 10;
            rs |= (self.read(CMOS_MEM_EXTMEM_HIGH)? as u32) << 18;
            rs += 1024 * 1024; // 1 MiB
        }

        Ok(rs)
    }

    /// Returns the high RAM size (memory over the 4 GiB mark)
    pub fn high_ram_size(&mut self) -> Result<u64, &'static str> {
        let mut high: u64 = (self.read(CMOS_MEM_HIGHMEM_LOW)? as u64) << 16;
        high |= (self.read(CMOS_MEM_HIGHMEM_MID)? as u64) << 24;
        high |= (self.read(CMOS_MEM_HIGHMEM_HIGH)? as u64) << 32;

        Ok(high)
    }

    fn read(&mut self, index: u8) -> Result<u8, &'static str> {
        // Safety: we've asked the caller to guarantee that these ports are exclusively available
        // when calling new(), so accessing them is safe.
        unsafe {
            self.index_port.try_write(index | NMI_DISABLE_BIT)?;
            self.data_port.try_read()
        }
    }
}
