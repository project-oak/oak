//
// Copyright 2023 The Project Oak Authors
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

use alloc::boxed::Box;

use oak_restricted_kernel_dice::DerivedKey;
use oak_restricted_kernel_interface::{DERIVED_KEY_FD, Errno};

use super::fd::{FileDescriptor, copy_max_slice};

#[derive(Default)]
struct DerivedKeyState {
    data: DerivedKey,
    index: usize,
}

enum DerivedKeyDescriptor {
    Readable(DerivedKeyState),
    Writeable(DerivedKeyState),
}

impl DerivedKeyDescriptor {
    fn new() -> Self {
        Self::Writeable(DerivedKeyState::default())
    }
}

impl FileDescriptor for DerivedKeyDescriptor {
    fn read(&mut self, buf: &mut [u8]) -> Result<isize, oak_restricted_kernel_interface::Errno> {
        match self {
            DerivedKeyDescriptor::Writeable(_write_state) => Err(Errno::EINVAL),
            DerivedKeyDescriptor::Readable(read_state) => {
                let data_as_slice = read_state.data.as_mut_slice();
                let length = copy_max_slice(&data_as_slice[read_state.index..], buf);
                read_state.index += length;
                Ok(length as isize)
            }
        }
    }

    fn write(&mut self, buf: &[u8]) -> Result<isize, oak_restricted_kernel_interface::Errno> {
        match self {
            DerivedKeyDescriptor::Readable(_read_state) => Err(Errno::EINVAL),
            DerivedKeyDescriptor::Writeable(write_state) => {
                let data_as_slice =
                    <DerivedKey as zerocopy::IntoBytes>::as_mut_bytes(&mut write_state.data);

                if buf.len() > data_as_slice[write_state.index..].len() {
                    // the key has a known size. If the app keeps writing to
                    // this FD after it has written all of it, it's doing something wrong.
                    return Err(Errno::EINVAL);
                }

                let length = copy_max_slice(buf, &mut data_as_slice[write_state.index..]);

                write_state.index += length;

                if write_state.index == data_as_slice.len() {
                    let derived_key =
                        <DerivedKey as zerocopy::FromBytes>::read_from_bytes(data_as_slice)
                            .unwrap();
                    let _ = core::mem::replace(
                        self,
                        Self::Readable(DerivedKeyState { index: 0, data: derived_key }),
                    );
                }

                Ok(length as isize)
            }
        }
    }

    fn sync(&mut self) -> Result<(), oak_restricted_kernel_interface::Errno> {
        Ok(())
    }
}

/// Registers a file descriptor for reading a derived key (0x21)
pub fn register() {
    super::fd::register(DERIVED_KEY_FD, Box::new(DerivedKeyDescriptor::new()))
        .map_err(|_| ()) // throw away the box
        .expect("DerivedKeyDescriptor already registered");
}
