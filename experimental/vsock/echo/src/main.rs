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

    let mut buffer = vec![];
    buffer.resize(BUFFER_SIZE, 0);
    loop {
        let read_bytes = match stream.read(&mut buffer) {
            Ok(0) => break,
            Ok(read_bytes) => read_bytes,
            Err(error) => panic!("Couldn't read bytes: {}", error),
        };
        println!("Received {:?} bytes", read_bytes);

        let mut write_bytes_sum = 0;
        while write_bytes_sum < read_bytes {
            let write_bytes = match stream.write(&buffer[write_bytes_sum..read_bytes]) {
                Ok(0) => break,
                Ok(write_bytes) => write_bytes,
                Err(error) => panic!("Couldn't write bytes: {}", error),
            };
            write_bytes_sum += write_bytes;
        }
    }

    stream
        .shutdown(Shutdown::Both)
        .expect("Couldn't shutdown stream");
}
