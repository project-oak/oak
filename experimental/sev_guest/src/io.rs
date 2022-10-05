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

use crate::ghcb::{Ghcb, GhcbProtocol};
use core::marker::PhantomData;
use lock_api::{Mutex, RawMutex};
use x86_64::instructions::port::{PortReadOnly, PortWriteOnly};

/// Factory for instantiating IO port readers and writers.
///
/// The typical usage is to either create raw instances that peform direct IO on the ports, or
/// instances that use the GHCB IOIO protocol.
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
    /// This function is unsafe because port access could have unsafe side-effects.
    unsafe fn try_read(&mut self) -> Result<T, &'static str>;
}

/// Writer that can be used to write values to a port.
pub trait PortWriter<T> {
    /// Tries to write a value to the port.
    ///
    /// # Safety
    ///
    /// This function is unsafe because port access could have unsafe side-effects.
    unsafe fn try_write(&mut self, value: T) -> Result<(), &'static str>;
}

/// A factory for creating port readers and writers that use the GHCB IOIO protocol.
pub struct GhcbIoFactory<
    'a,
    R: RawMutex + 'a,
    P: AsMut<GhcbProtocol<'a, G>> + 'a + ?Sized,
    G: AsMut<Ghcb> + AsRef<Ghcb> + ?Sized + 'a,
> {
    ghcb_protocol: &'a Mutex<R, P>,
    _phantom: PhantomData<G>,
}

impl<'a, R, P, G> GhcbIoFactory<'a, R, P, G>
where
    R: RawMutex + 'a,
    P: AsMut<GhcbProtocol<'a, G>> + 'a + ?Sized,
    G: AsMut<Ghcb> + AsRef<Ghcb> + ?Sized + 'a,
{
    pub fn new(ghcb_protocol: &'a Mutex<R, P>) -> Self {
        GhcbIoFactory {
            ghcb_protocol,
            _phantom: PhantomData,
        }
    }
}

impl<'a, T, R, P, G> IoPortFactory<'a, T, GhcbIoPort<'a, R, P, G>, GhcbIoPort<'a, R, P, G>>
    for GhcbIoFactory<'a, R, P, G>
where
    R: RawMutex + 'a,
    P: AsMut<GhcbProtocol<'a, G>> + 'a + ?Sized,
    G: AsMut<Ghcb> + AsRef<Ghcb> + ?Sized + 'a,
    GhcbIoPort<'a, R, P, G>: PortReader<T> + PortWriter<T>,
{
    fn new_reader(&self, port: u16) -> GhcbIoPort<'a, R, P, G> {
        GhcbIoPort {
            ghcb_protocol: self.ghcb_protocol,
            port,
            _phantom: PhantomData,
        }
    }

    fn new_writer(&self, port: u16) -> GhcbIoPort<'a, R, P, G> {
        GhcbIoPort {
            ghcb_protocol: self.ghcb_protocol,
            port,
            _phantom: PhantomData,
        }
    }
}

/// GHCB-based wrapper for a single IO port.
pub struct GhcbIoPort<
    'a,
    R: RawMutex + 'a,
    P: AsMut<GhcbProtocol<'a, G>> + 'a + ?Sized,
    G: AsMut<Ghcb> + AsRef<Ghcb> + ?Sized + 'a,
> {
    ghcb_protocol: &'a Mutex<R, P>,
    port: u16,
    _phantom: PhantomData<G>,
}

impl<'a, R, P, G> PortReader<u8> for GhcbIoPort<'a, R, P, G>
where
    R: RawMutex + 'a,
    P: AsMut<GhcbProtocol<'a, G>> + 'a + ?Sized,
    G: AsMut<Ghcb> + AsRef<Ghcb> + ?Sized + 'a,
{
    unsafe fn try_read(&mut self) -> Result<u8, &'static str> {
        self.ghcb_protocol.lock().as_mut().io_read_u8(self.port)
    }
}

impl<'a, R, P, G> PortReader<u32> for GhcbIoPort<'a, R, P, G>
where
    R: RawMutex + 'a,
    P: AsMut<GhcbProtocol<'a, G>> + 'a + ?Sized,
    G: AsMut<Ghcb> + AsRef<Ghcb> + ?Sized + 'a,
{
    unsafe fn try_read(&mut self) -> Result<u32, &'static str> {
        self.ghcb_protocol.lock().as_mut().io_read_u32(self.port)
    }
}

impl<'a, R, P, G> PortWriter<u8> for GhcbIoPort<'a, R, P, G>
where
    R: RawMutex + 'a,
    P: AsMut<GhcbProtocol<'a, G>> + 'a + ?Sized,
    G: AsMut<Ghcb> + AsRef<Ghcb> + ?Sized + 'a,
{
    unsafe fn try_write(&mut self, value: u8) -> Result<(), &'static str> {
        self.ghcb_protocol
            .lock()
            .as_mut()
            .io_write_u8(self.port, value)
    }
}

impl<'a, R, P, G> PortWriter<u32> for GhcbIoPort<'a, R, P, G>
where
    R: RawMutex + 'a,
    P: AsMut<GhcbProtocol<'a, G>> + 'a + ?Sized,
    G: AsMut<Ghcb> + AsRef<Ghcb> + ?Sized + 'a,
{
    unsafe fn try_write(&mut self, value: u32) -> Result<(), &'static str> {
        self.ghcb_protocol
            .lock()
            .as_mut()
            .io_write_u32(self.port, value)
    }
}

/// Factory for creating port reader and writers that perform direct raw IO operations.
pub struct RawIoPortFactory;

impl<'a, T> IoPortFactory<'a, T, PortReadOnly<T>, PortWriteOnly<T>> for RawIoPortFactory
where
    T: 'a,
    PortReadOnly<T>: PortReader<T>,
    PortWriteOnly<T>: PortWriter<T>,
{
    fn new_reader(&self, port: u16) -> PortReadOnly<T> {
        PortReadOnly::<T>::new(port)
    }

    fn new_writer(&self, port: u16) -> PortWriteOnly<T> {
        PortWriteOnly::<T>::new(port)
    }
}

impl PortReader<u8> for PortReadOnly<u8> {
    unsafe fn try_read(&mut self) -> Result<u8, &'static str> {
        Ok(self.read())
    }
}

impl PortReader<u32> for PortReadOnly<u32> {
    unsafe fn try_read(&mut self) -> Result<u32, &'static str> {
        Ok(self.read())
    }
}

impl PortWriter<u8> for PortWriteOnly<u8> {
    unsafe fn try_write(&mut self, value: u8) -> Result<(), &'static str> {
        self.write(value);
        Ok(())
    }
}

impl PortWriter<u32> for PortWriteOnly<u32> {
    unsafe fn try_write(&mut self, value: u32) -> Result<(), &'static str> {
        self.write(value);
        Ok(())
    }
}
