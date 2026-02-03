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

use oak_dice::evidence::{RestrictedKernelDiceData, Stage0DiceData};
use oak_restricted_kernel_interface::{DICE_DATA_FD, Errno};
use zeroize::Zeroize;

use super::fd::{FileDescriptor, copy_max_slice};

pub enum DiceData {
    Layer0(Box<Stage0DiceData>),
    Layer1(Box<RestrictedKernelDiceData>),
}

impl DiceData {
    fn as_mut_slice(&mut self) -> &mut [u8] {
        match self {
            DiceData::Layer0(stage0_dice_data) => {
                <Stage0DiceData as zerocopy::IntoBytes>::as_mut_bytes(stage0_dice_data)
            }
            DiceData::Layer1(stage1_dice_data) => {
                <RestrictedKernelDiceData as zerocopy::IntoBytes>::as_mut_bytes(stage1_dice_data)
            }
        }
    }
}

struct ReadState {
    data: DiceData,
    index: usize,
}

struct WriteState {
    data: RestrictedKernelDiceData,
    index: usize,
}

enum DiceDataDescriptor {
    Readable(Box<ReadState>),
    Writeable(Box<WriteState>),
}

impl DiceDataDescriptor {
    fn new(data: DiceData) -> Self {
        Self::Readable(Box::new(ReadState { index: 0, data }))
    }
}

impl FileDescriptor for DiceDataDescriptor {
    fn read(&mut self, buf: &mut [u8]) -> Result<isize, oak_restricted_kernel_interface::Errno> {
        match self {
            DiceDataDescriptor::Writeable(_write_state) => Err(Errno::EINVAL),
            DiceDataDescriptor::Readable(read_state) => {
                let data_as_slice = read_state.data.as_mut_slice();
                let length = copy_max_slice(&data_as_slice[read_state.index..], buf);

                // destroy the data that was read, to ensure that it can only be read once
                let slice_to_read =
                    &mut data_as_slice[read_state.index..(read_state.index + length)];
                slice_to_read.zeroize();

                read_state.index += length;
                Ok(length as isize)
            }
        }
    }

    fn write(&mut self, buf: &[u8]) -> Result<isize, oak_restricted_kernel_interface::Errno> {
        match self {
            DiceDataDescriptor::Readable(read_state) => match &mut read_state.data {
                DiceData::Layer0(stage0_dice_data) => {
                    <Stage0DiceData as zerocopy::IntoBytes>::as_mut_bytes(stage0_dice_data)
                        .zeroize();
                    let _ = core::mem::replace(
                        self,
                        Self::Writeable(Box::new(WriteState {
                            index: 0,
                            data: <RestrictedKernelDiceData as zerocopy::FromZeros>::new_zeroed(),
                        })),
                    );
                    self.write(buf)
                }
                _ => Err(Errno::EINVAL),
            },
            DiceDataDescriptor::Writeable(write_state) => {
                let data_as_slice = <RestrictedKernelDiceData as zerocopy::IntoBytes>::as_mut_bytes(
                    &mut write_state.data,
                );

                if buf.len() > data_as_slice[write_state.index..].len() {
                    // the dice data the app may write has a known size. If the app keeps writing to
                    // this FD after it has written all of it, it's doing something wrong.
                    return Err(Errno::EINVAL);
                }

                let length = copy_max_slice(buf, &mut data_as_slice[write_state.index..]);

                write_state.index += length;

                if write_state.index == data_as_slice.len() {
                    let read_data =
                        <RestrictedKernelDiceData as zerocopy::FromBytes>::read_from_bytes(
                            data_as_slice,
                        )
                        .unwrap();
                    let _ = core::mem::replace(
                        self,
                        Self::Readable(Box::new(ReadState {
                            index: 0,
                            data: DiceData::Layer1(Box::new(read_data)),
                        })),
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

/// Registers a file descriptor for reading dice data
pub fn register(data: DiceData) {
    super::fd::register(DICE_DATA_FD, Box::new(DiceDataDescriptor::new(data)))
        .map_err(|_| ()) // throw away the box
        .expect("DiceDataDescriptor already registered");
}

#[test]
fn fd_permits_one_full_write() {
    let layer0 = <Stage0DiceData as zerocopy::FromZeroes>::new_zeroed();
    let layer1 = <RestrictedKernelDiceData as zerocopy::FromZeroes>::new_zeroed();

    let mut fd = DiceDataDescriptor::new(DiceData::Layer0(Box::new(layer0)));

    {
        let mut buf: [u8; 1] = [5; 1];
        assert!(fd.read(&mut buf).is_ok());
        assert!(buf[0] == 0);
    }

    assert!(fd.write(<RestrictedKernelDiceData as zerocopy::AsBytes>::as_bytes(&layer1)).is_ok());

    {
        let mut buf: [u8; 1] = [5; 1];
        assert!(fd.read(&mut buf).is_ok());
        assert!(buf[0] == 0);
    }

    assert!(fd.write(<RestrictedKernelDiceData as zerocopy::AsBytes>::as_bytes(&layer1)).is_err());
}

#[test]
fn fd_supports_partial_writes() {
    let layer0 = <Stage0DiceData as zerocopy::FromZeroes>::new_zeroed();
    let layer1 = <RestrictedKernelDiceData as zerocopy::FromZeroes>::new_zeroed();

    let mut fd = DiceDataDescriptor::new(DiceData::Layer0(Box::new(layer0)));

    let layer1_bytes = <RestrictedKernelDiceData as zerocopy::AsBytes>::as_bytes(&layer1);
    let halfway_point = layer1_bytes.len() / 2;

    assert!(fd.write(&layer1_bytes[..halfway_point]).is_ok());
    {
        // reading should fail if data hasn't been fully written yet
        let mut buf: [u8; 1] = [5; 1];
        assert!(fd.read(&mut buf).is_err());
    };
    assert!(fd.write(&layer1_bytes[halfway_point..]).is_ok());

    assert!(fd.write(&layer1_bytes[..1]).is_err());

    {
        let mut buf: [u8; 1] = [5; 1];
        assert!(fd.read(&mut buf).is_ok());
    };
}
