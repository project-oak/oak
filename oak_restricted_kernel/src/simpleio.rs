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

use crate::mm::page_tables::DirectMap;
use alloc::collections::VecDeque;
use oak_simple_io::SimpleIo;
use sev_guest::io::PortFactoryWrapper;
use x86_64::{structures::paging::Translate, VirtAddr};

/// A communications channel using a simple IO device.
pub struct SimpleIoChannel {
    /// The simple IO device.
    device: SimpleIo,
    /// A buffer to temporarily store extra data from the device that was not fully read when using
    /// `read`. This could happen if the device sent more bytes in a single buffer than was
    /// expected by `read`.
    pending_data: Option<VecDeque<u8>>,
}

impl SimpleIoChannel {
    pub fn new(mapper: &DirectMap) -> Self {
        let io_port_factory = PortFactoryWrapper::new_raw();
        let device = SimpleIo::new_with_defaults(io_port_factory, |vaddr: VirtAddr| {
            (mapper as &dyn Translate).translate_addr(vaddr)
        })
        .expect("couldn't create IO device");
        let pending_data = None;
        Self {
            device,
            pending_data,
        }
    }

    /// Tries once to fill the destination with as much data as is currently available, either in
    /// the pending buffer (if data was left over from the previous read), or from the next
    /// available buffer in the device if there was no data in the pending buffer.
    ///
    /// If data is read from the device and not fully used the remainder is stored back into the
    /// pending buffer.
    ///
    /// Returns the number of bytes read if any data was available to read.
    fn read_partial(&mut self, dest: &mut [u8]) -> Option<usize> {
        let mut source = match self.pending_data.take() {
            Some(data) => data,
            None => self.device.read_bytes()?,
        };

        let len = dest.len();
        let mut position = 0;
        while position < len {
            if let Some(byte) = source.pop_front() {
                dest[position] = byte;
                position += 1;
            } else {
                break;
            }
        }

        if !source.is_empty() {
            self.pending_data.replace(source);
        }
        Some(position)
    }
}

impl oak_channel::Write for SimpleIoChannel {
    fn write(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let mut start = 0;
        let data_len = data.len();
        while start < data_len {
            let count = self.device.write_bytes(&data[start..]).unwrap_or(0);
            start += count;
        }
        Ok(())
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        // We always flush on write, so do nothing.
        Ok(())
    }
}

impl oak_channel::Read for SimpleIoChannel {
    fn read(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        let len = data.len();
        let mut count = 0;
        while count < len {
            count += self.read_partial(&mut data[count..]).unwrap_or(0);
        }

        Ok(())
    }
}
