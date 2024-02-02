//
// Copyright 2024 The Project Oak Authors
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

#![cfg_attr(not(feature = "std"), no_std)]
#![feature(array_chunks)]

pub mod basic_framed;

extern crate alloc;

/// Simple no_std compatible equivalent of [`std::io::Read`].
///
/// [`std::io::Read`]: <https://doc.rust-lang.org/std/io/trait.Read.html>
pub trait Read {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()>;
}

#[cfg(feature = "std")]
impl<T: std::io::Read> Read for T {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        self.read_exact(data).map_err(anyhow::Error::msg)
    }
}

/// Simple no_std compatible equivalent of [`std::io::Write`].
///
/// [`std::io::Write`]: <https://doc.rust-lang.org/std/io/trait.Write.html>
pub trait Write {
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()>;
    fn flush(&mut self) -> anyhow::Result<()>;
}

#[cfg(feature = "std")]
impl<T: std::io::Write> Write for T {
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        self.write_all(data).map_err(anyhow::Error::msg)
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        std::io::Write::flush(self).map_err(anyhow::Error::msg)
    }
}

pub trait Channel: Read + Write + Send + Sync {}

impl<T: Read + Write + Send + Sync> Channel for T {}
