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

use core::alloc::Allocator;

use log::info;
use oak_channel::{Read, Write};
use rust_hypervisor_firmware_virtio::pci::VirtioPciTransport;
use x86_64::{PhysAddr, VirtAddr};

use crate::mm::Translator;

// The virtio vsock port on which to listen.
#[cfg(feature = "vsock_channel")]
const VSOCK_PORT: u32 = 1024;

pub struct Channel<T> {
    inner: T,
}

impl<T> Read for Channel<T>
where
    T: oak_virtio::Read,
{
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        self.inner.read_exact(data)
    }
}

impl<T> Write for Channel<T>
where
    T: oak_virtio::Write,
{
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        self.inner.write_all(data)
    }
    fn flush(&mut self) -> anyhow::Result<()> {
        self.inner.flush()
    }
}

#[cfg(feature = "vsock_channel")]
pub fn get_vsock_channel<A: Allocator>(
    alloc: &A,
) -> Channel<oak_virtio::vsock::socket::Socket<'_, VirtioPciTransport, A>> {
    use crate::PAGE_TABLES;
    let pt_guard = PAGE_TABLES.lock();
    let vsock = oak_virtio::vsock::VSock::find_and_configure_device(
        |vaddr: VirtAddr| pt_guard.get().unwrap().translate_virtual(vaddr),
        |paddr: PhysAddr| pt_guard.get().unwrap().translate_physical(paddr),
        alloc,
    )
    .expect("couldn't configure PCI virtio vsock device");
    info!("Socket device status: {}", vsock.get_status());
    let listener = oak_virtio::vsock::socket::SocketListener::new(vsock, VSOCK_PORT);
    Channel { inner: listener.accept().expect("couldn't accept connection") }
}
