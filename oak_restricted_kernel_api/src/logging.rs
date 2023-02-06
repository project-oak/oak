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

use core::fmt::Write;

use crate::syscall::{fsync, write};

struct Stderr {}

impl Stderr {
    const STDERR_FD: i32 = 2;

    fn flush() {
        fsync(Self::STDERR_FD).unwrap();
    }
}

impl core::fmt::Write for Stderr {
    fn write_str(&mut self, s: &str) -> Result<(), core::fmt::Error> {
        let buf = s.as_bytes();
        let mut written = 0;
        while written < s.len() {
            written += write(Self::STDERR_FD, &buf[written..]).unwrap();
        }

        Ok(())
    }
}

pub struct StderrLogger {}

impl log::Log for StderrLogger {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        writeln!(Stderr {}, "{}: {}", record.level(), record.args()).unwrap();
    }

    fn flush(&self) {
        Stderr::flush();
    }
}
