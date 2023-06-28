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

#![feature(file_create_new)]

use log::{debug, info};
use nix::sys::termios::{cfmakeraw, tcgetattr, tcsetattr, SetArg};
use std::{
    fs::OpenOptions,
    io::{Read, Seek, Write},
    os::fd::{AsRawFd, RawFd},
};

mod init;

// The path that identifies the first Virtio Console port.
const DEVICE_PATH: &str = "/dev/hvc0";

// The path to the physical memory device we will use to read the DICE data.
const DICE_PATH: &str = "/dev/mem";
// The physical address of the start of the DICE data in memory.
const DICE_OFFSET: u64 = 0x1000;
// The number of bytes we will read from the DICE data.
const DICE_SIZE: usize = 64;

fn main() -> ! {
    simple_logger::SimpleLogger::new().init().unwrap();
    // Set up the Linux environment, since we expect to be the initial process.
    init::init().unwrap();

    info!("Echo app started");

    let mut dice_reader = OpenOptions::new()
        .read(true)
        .open(DICE_PATH)
        .expect("couldn't open DICE memory device for reading");
    let mut dice_data = [0u8; DICE_SIZE];
    dice_reader
        .seek(std::io::SeekFrom::Start(DICE_OFFSET))
        .expect("couldn't seek to DICE offset");
    dice_reader
        .read(&mut dice_data[..])
        .expect("couldn't read dice data");
    info!("DICE data: {:?}", dice_data);

    let mut buf = [0u8; 1024];
    // We use the first Virtio Console port for communications with the host.
    let mut reader = OpenOptions::new()
        .read(true)
        .open(DEVICE_PATH)
        .expect("couldn't open virtio console port for reading");

    // Enable raw mode so that Linux does not also echo back the values.
    set_console_to_raw_mode(reader.as_raw_fd());

    let mut writer = OpenOptions::new()
        .write(true)
        .open(DEVICE_PATH)
        .expect("couldn't open virtio console port for writing");

    debug!("Listening on port");
    loop {
        let len = reader.read(&mut buf[..]).expect("coulnd't read request");
        if len > 0 {
            debug!("Echoing {} bytes", len);
            writer
                .write_all(&buf[..len])
                .expect("couldn't write response");
        }
    }
}

fn set_console_to_raw_mode(fd: RawFd) {
    let mut attributes = tcgetattr(fd).expect("file descriptor does not represent a console");
    cfmakeraw(&mut attributes);
    tcsetattr(fd, SetArg::TCSANOW, &attributes).expect("couldn't set raw mode on console");
}
