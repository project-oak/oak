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

use std::{
    fs::OpenOptions,
    io::{Read, Write},
    os::fd::AsFd,
};

use log::{debug, info};
use nix::sys::termios::{cfmakeraw, tcgetattr, tcsetattr, SetArg};

mod init;

// The path that identifies the first Virtio Console port.
const DEVICE_PATH: &str = "/dev/hvc0";

fn main() -> ! {
    simple_logger::SimpleLogger::new().init().unwrap();
    // Set up the Linux environment, since we expect to be the initial process.
    init::init().unwrap();

    info!("Echo app started");

    let mut buf = [0u8; 1024];
    // We use the first Virtio Console port for communications with the host.
    let mut reader = OpenOptions::new()
        .read(true)
        .open(DEVICE_PATH)
        .expect("couldn't open virtio console port for reading");

    // Enable raw mode so that Linux does not also echo back the values.
    set_console_to_raw_mode(reader.as_fd());

    let mut writer = OpenOptions::new()
        .write(true)
        .open(DEVICE_PATH)
        .expect("couldn't open virtio console port for writing");

    debug!("Listening on port");
    loop {
        let len = reader.read(&mut buf[..]).expect("coulnd't read request");
        if len > 0 {
            debug!("Echoing {} bytes", len);
            writer.write_all(&buf[..len]).expect("couldn't write response");
        }
    }
}

fn set_console_to_raw_mode<Fd: AsFd>(fd: Fd) {
    let mut attributes = tcgetattr(&fd).expect("file descriptor does not represent a console");
    cfmakeraw(&mut attributes);
    tcsetattr(fd, SetArg::TCSANOW, &attributes).expect("couldn't set raw mode on console");
}
