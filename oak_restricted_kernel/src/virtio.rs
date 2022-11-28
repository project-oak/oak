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

use crate::mm::Translator;
use core::alloc::Allocator;
use log::info;
use oak_channel::{Read, Write};
use rust_hypervisor_firmware_virtio::pci::VirtioPciTransport;
use x86_64::{PhysAddr, VirtAddr};

// The virtio vsock port on which to listen.
#[cfg(feature = "vsock_channel")]
const VSOCK_PORT: u32 = 1024;

pub struct Channel<T> {
    pub(crate) inner: T,
}

impl<T> Read for Channel<T>
where
    T: oak_virtio::Read,
{
    fn read(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        self.inner.read(data)
    }
}

impl<T> Write for Channel<T>
where
    T: oak_virtio::Write,
{
    fn write(&mut self, data: &[u8]) -> anyhow::Result<()> {
        self.inner.write(data)
    }
    fn flush(&mut self) -> anyhow::Result<()> {
        self.inner.flush()
    }
}

#[cfg(feature = "virtio_console_channel")]
pub fn get_console_channel<'a, X: Translator, A: Allocator>(
    translator: &X,
    alloc: &'a A,
) -> Channel<oak_virtio::console::Console<'a, VirtioPciTransport, A>> {
    let console = oak_virtio::console::Console::find_and_configure_device(
        |vaddr: VirtAddr| translator.translate_virtual(vaddr),
        |paddr: PhysAddr| translator.translate_physical(paddr),
        alloc,
    )
    .expect("couldn't configure PCI virtio console device");
    info!("Console device status: {}", console.get_status());
    Channel { inner: console }
}

#[cfg(feature = "vsock_channel")]
pub fn get_vsock_channel<'a, X: Translator, A: Allocator>(
    translator: &X,
    alloc: &'a A,
) -> Channel<oak_virtio::vsock::socket::Socket<'a, VirtioPciTransport, A>> {
    let vsock = oak_virtio::vsock::VSock::find_and_configure_device(
        |vaddr: VirtAddr| translator.translate_virtual(vaddr),
        |paddr: PhysAddr| translator.translate_physical(paddr),
        alloc,
    )
    .expect("couldn't configure PCI virtio vsock device");
    info!("Socket device status: {}", vsock.get_status());
    let listener = oak_virtio::vsock::socket::SocketListener::new(vsock, VSOCK_PORT);
    Channel {
        inner: listener.accept().expect("couldn't accept connection"),
    }
}
