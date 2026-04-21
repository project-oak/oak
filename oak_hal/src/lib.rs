//
// Copyright 2026 The Project Oak Authors
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

#![no_std]

use x86_64::{
    instructions::port::Port,
    structures::port::{PortRead, PortWrite},
};

/// Factory for instantiating IO port readers and writers.
pub trait IoPortFactory<'a, T, R: PortReader<T> + 'a, W: PortWriter<T> + 'a> {
    /// Creates a new IO port reader instance.
    fn new_reader(&self, port: u16) -> R;
    /// Creates a new IO port writer instance.
    fn new_writer(&self, port: u16) -> W;
}

/// Reader that can be used to read values from a port.
pub trait PortReader<T> {
    /// Tries to read from the port.
    ///
    /// # Safety
    ///
    /// This function is unsafe because port access could have unsafe
    /// side-effects.
    unsafe fn try_read(&mut self) -> Result<T, &'static str>;
}

/// Writer that can be used to write values to a port.
pub trait PortWriter<T> {
    /// Tries to write a value to the port.
    ///
    /// # Safety
    ///
    /// This function is unsafe because port access could have unsafe
    /// side-effects.
    unsafe fn try_write(&mut self, value: T) -> Result<(), &'static str>;
}

impl<T> PortReader<T> for Port<T>
where
    T: PortRead,
{
    unsafe fn try_read(&mut self) -> Result<T, &'static str> {
        Ok(unsafe { self.read() })
    }
}

impl<T> PortWriter<T> for Port<T>
where
    T: PortWrite,
{
    unsafe fn try_write(&mut self, value: T) -> Result<(), &'static str> {
        unsafe { self.write(value) };
        Ok(())
    }
}
