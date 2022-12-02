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

use core::{cmp::min, ffi::CStr};
use oak_sev_guest::io::{IoPortFactory, PortFactoryWrapper, PortReader, PortWrapper, PortWriter};
use zerocopy::{AsBytes, FromBytes};

// See https://www.qemu.org/docs/master/specs/fw_cfg.html for documentation about the various data structures and constants.
const FWCFG_PORT_SELECTOR: u16 = 0x510;
const FWCFG_PORT_DATA: u16 = 0x511;

const SIGNATURE: &[u8] = b"QEMU";

#[repr(u16)]
enum FwCfgItems {
    Signature = 0x0000,
    FileDir = 0x0019,
    E820ReservationTable = 0x8003,
}

/// an individual file entry, 64 bytes total
#[repr(C)]
#[derive(AsBytes, FromBytes)]
pub struct DirEntry {
    /// size of referenced fw_cfg item, big-endian
    size: u32,
    /// selector key of fw_cfg item, big-endian
    select: u16,
    _reserved: u16,
    /// fw_cfg item name, NUL-terminated ascii
    name: [u8; 56],
}
static_assertions::assert_eq_size!(DirEntry, [u8; 64usize]);

impl Default for DirEntry {
    fn default() -> Self {
        Self {
            size: 0,
            select: 0,
            _reserved: 0,
            name: [0; 56],
        }
    }
}

impl DirEntry {
    pub fn name(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.name).unwrap()
    }

    pub fn size(&self) -> usize {
        u32::from_be(self.size) as usize
    }

    pub fn selector(&self) -> u16 {
        u16::from_be(self.select)
    }
}

impl core::fmt::Debug for DirEntry {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("DirEntry")
            .field("name", &self.name())
            .field("size", &self.size())
            .field("select", &self.selector())
            .finish()
    }
}

/// Wrapper for the QEMU Firmware Configuration device.
///
/// See <https://www.qemu.org/docs/master/specs/fw_cfg.html> for more details.
pub struct FwCfg {
    selector: PortWrapper<u16>,
    data: PortWrapper<u8>,
}

impl FwCfg {
    /// # Safety
    ///
    /// While we do probe for the existence of the QEMU fw_cfg device, reading or writing to I/O
    /// ports that are not in use is inherently undefined behaviour. What's worse, if there happens
    /// to be some other device using those I/O ports, the results are completely unknowable.
    ///
    /// The caller has to guarantee that at least doing the probe will not cause any adverse
    /// effects.
    pub unsafe fn new(port_factory: PortFactoryWrapper) -> Result<Self, &'static str> {
        let mut fwcfg = Self {
            selector: port_factory.new_writer(FWCFG_PORT_SELECTOR),
            data: port_factory.new_reader(FWCFG_PORT_DATA),
        };

        // Make sure the fw_cfg device is available. If the device is not available, writing and
        // reading to I/O ports is undefined behaviour.
        fwcfg.write_selector(FwCfgItems::Signature as u16)?;
        let mut signature = [0u8; SIGNATURE.len()];
        fwcfg.read(&mut signature)?;

        if signature == SIGNATURE {
            Ok(fwcfg)
        } else {
            Err("QEMU fw_cfg device not available")
        }
    }

    /// Returns an iterator over the files in the fw_cfg system.
    ///
    /// # Safety
    ///
    /// You should consume the iterator fully before calling any other methods of this struct, or at
    /// the very least don't use the iterator after calling some other function.
    /// (This means that, for example, you shouldn't try to read the files while iterating over the
    /// directory contents.)
    /// If you call any other methods, the iterator will be in an undefined state and unsafe to read
    /// from.
    pub unsafe fn dir(&mut self) -> impl Iterator<Item = DirEntry> + '_ {
        self.write_selector(FwCfgItems::FileDir as u16).unwrap();

        // We don't represent FwCfgFiles as a struct, as you can't do that in safe Rust. Therefore,
        // read fields individually.
        let count = {
            let mut buf = [0u8; 4];
            self.read(&mut buf).unwrap();
            u32::from_be_bytes(buf)
        };

        (0..count).map(|_| {
            let mut file = DirEntry::default();
            self.read(&mut file).unwrap();
            file
        })
    }

    pub fn find(&mut self, name: &CStr) -> Option<DirEntry> {
        // Safety: this is safe as we don't leak the iterator.
        unsafe { self.dir() }.find(|file| file.name() == name)
    }

    /// Reads the contents of a file to a predetermined struct.
    /// Returns the number of bytes read.
    ///
    /// # Safety
    ///
    /// While we will never write beyond the memory allocated to `object`, it is up to the caller to
    /// ensure that the type of `object` is a faithful representation of the contents of the file;
    /// otherwise, `object` may be left in an invalid state.
    pub unsafe fn read_file_by_name<T: AsBytes + FromBytes>(
        &mut self,
        name: &CStr,
        object: &mut T,
    ) -> Result<usize, &'static str> {
        let mut entry: Option<DirEntry> = None;
        for file in self.dir() {
            if file.name() != name {
                continue;
            };
            entry = Some(file);
            break;
        }
        if let Some(file) = entry {
            self.read_file(&file, object.as_bytes_mut())
        } else {
            Err("couldn't find requested file")
        }
    }

    /// Reads the size of the E820 reservation table.
    ///
    /// This table predates the file interface and thus has its own selector.
    pub fn read_e820_reservation_table_size(&mut self) -> Result<u32, &'static str> {
        let mut reservation_count: u32 = 0;
        self.write_selector(FwCfgItems::E820ReservationTable as u16)?;
        self.read(&mut reservation_count)?;
        Ok(reservation_count)
    }

    /// Reads contents of a file; returns the number of bytes actrually read.
    ///
    /// The buffer `buf` will be filled to capacity if the file is larger;
    /// if it is shorter, the trailing bytes will not be touched.
    pub fn read_file(&mut self, file: &DirEntry, buf: &mut [u8]) -> Result<usize, &'static str> {
        self.write_selector(file.selector())?;
        let len = min(buf.len(), file.size());
        self.read_buf(&mut buf[..len])?;
        Ok(len)
    }

    fn write_selector(&mut self, selector: u16) -> Result<(), &'static str> {
        // Safety: we make sure the device is available when initializing FwCfg.
        unsafe { self.selector.try_write(selector) }
    }

    fn read<T: AsBytes + FromBytes>(&mut self, object: &mut T) -> Result<(), &'static str> {
        self.read_buf(object.as_bytes_mut())
    }

    fn read_buf(&mut self, buf: &mut [u8]) -> Result<(), &'static str> {
        for i in buf {
            // Safety: We make sure that the device is available in `new()`, so reading from the
            // port is safe.
            *i = unsafe { self.data.try_read() }?;
        }
        Ok(())
    }
}
