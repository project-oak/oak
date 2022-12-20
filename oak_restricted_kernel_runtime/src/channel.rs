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

use anyhow::anyhow;
use oak_channel::{Read, Write};

pub const OAK_CHANNEL_FD: i32 = 10;

pub struct SyscallChannel {
    fd: i32,
}

impl SyscallChannel {
    pub fn new(fd: i32) -> Self {
        Self { fd }
    }
}

impl Default for SyscallChannel {
    fn default() -> Self {
        Self::new(OAK_CHANNEL_FD)
    }
}

impl Read for SyscallChannel {
    fn read(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        let len = data.len();
        let mut remaining = data.len();

        while remaining > 0 {
            let ptr = data[len - remaining..].as_mut_ptr();
            remaining -= crate::syscall::read(self.fd, ptr, remaining)
                .map_err(|err| anyhow!("read failure: {}", err))?;
        }

        Ok(())
    }
}

impl Write for SyscallChannel {
    fn write(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let len = data.len();
        let mut remaining = data.len();

        while remaining > 0 {
            let ptr = data[len - remaining..].as_ptr();
            remaining -= crate::syscall::write(self.fd, ptr, remaining)
                .map_err(|err| anyhow!("write failure: {}", err))?;
        }

        Ok(())
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        crate::syscall::fsync(self.fd).map_err(|err| anyhow!("sync failure: {}", err))
    }
}
