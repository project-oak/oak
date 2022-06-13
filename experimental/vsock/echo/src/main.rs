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

use libc::c_int;
use std::{
    io::{Read, Write},
    net::Shutdown,
    os::unix::io::FromRawFd,
};
use vsock::VsockStream;

const FILE_DESCRIPTOR: c_int = 1023;
const BUFFER_SIZE: usize = 1024;

fn main() {
    let mut stream;
    unsafe {
        stream = VsockStream::from_raw_fd(FILE_DESCRIPTOR);
    }
    println!(
        "Connected to the {}",
        stream.peer_addr().expect("Couldn't get peer address")
    );

    let mut buffer = vec![0; BUFFER_SIZE];
    loop {
        let read_bytes = stream.read(&mut buffer).expect("Couldn't read bytes");
        if read_bytes == 0 {
            break // Stream has finished.
        }
        println!("Received {:?} bytes", read_bytes);

        stream.write_all(&buffer[..read_bytes]).expect("Couldn't write bytes");
    }

    stream
        .shutdown(Shutdown::Both)
        .expect("Couldn't shutdown stream");
}
