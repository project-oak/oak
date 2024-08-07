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

use x86_64::structures::port::{PortRead, PortWrite};

use super::GHCB_WRAPPER;

pub trait GhcbPortRead: PortRead {
    unsafe fn read_from_port(port: u16) -> Result<Self, &'static str>
    where
        Self: Sized;
}

pub trait GhcbPortWrite: PortWrite {
    unsafe fn write_to_port(port: u16, value: Self) -> Result<(), &'static str>
    where
        Self: Sized;
}

impl GhcbPortRead for u8 {
    unsafe fn read_from_port(port: u16) -> Result<Self, &'static str> {
        if let Some(mut ghcb) = GHCB_WRAPPER.get() {
            ghcb.io_read_u8(port)
        } else {
            Ok(<u8 as PortRead>::read_from_port(port))
        }
    }
}

impl GhcbPortWrite for u8 {
    unsafe fn write_to_port(port: u16, value: Self) -> Result<(), &'static str>
    where
        Self: Sized,
    {
        if let Some(mut ghcb) = GHCB_WRAPPER.get() {
            ghcb.io_write_u8(port, value)
        } else {
            <u8 as PortWrite>::write_to_port(port, value);
            Ok(())
        }
    }
}

impl GhcbPortRead for u16 {
    unsafe fn read_from_port(port: u16) -> Result<Self, &'static str> {
        if let Some(mut ghcb) = GHCB_WRAPPER.get() {
            ghcb.io_read_u16(port)
        } else {
            Ok(<u16 as PortRead>::read_from_port(port))
        }
    }
}

impl GhcbPortWrite for u16 {
    unsafe fn write_to_port(port: u16, value: Self) -> Result<(), &'static str>
    where
        Self: Sized,
    {
        if let Some(mut ghcb) = GHCB_WRAPPER.get() {
            ghcb.io_write_u16(port, value)
        } else {
            <u16 as PortWrite>::write_to_port(port, value);
            Ok(())
        }
    }
}

impl GhcbPortRead for u32 {
    unsafe fn read_from_port(port: u16) -> Result<Self, &'static str> {
        if let Some(mut ghcb) = GHCB_WRAPPER.get() {
            ghcb.io_read_u32(port)
        } else {
            Ok(<u32 as PortRead>::read_from_port(port))
        }
    }
}

impl GhcbPortWrite for u32 {
    unsafe fn write_to_port(port: u16, value: Self) -> Result<(), &'static str>
    where
        Self: Sized,
    {
        if let Some(mut ghcb) = GHCB_WRAPPER.get() {
            ghcb.io_write_u32(port, value)
        } else {
            <u32 as PortWrite>::write_to_port(port, value);
            Ok(())
        }
    }
}
