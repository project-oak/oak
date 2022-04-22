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

extern crate alloc;

use alloc::vec::Vec;
use ciborium::{de, ser};
use crate::Channel;

#[derive(Debug)]
pub enum Error<T> {
    // An error occured while deserializing.
    De(ciborium::de::Error<T>),

    // An error occured while serializing.
    Ser(ciborium::ser::Error<T>),
}

impl<E> ciborium_io::Write for &mut dyn Channel<Error = E> {
    type Error = E;

    fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        self.send(data)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl<E> ciborium_io::Read for &mut dyn Channel<Error = E> {
    type Error = E;

    fn read_exact(&mut self, data: &mut [u8]) -> Result<(), Self::Error> {
        self.recv(data)
    }
}

// Echoes all input on the interface back out.
pub fn echo<E: core::fmt::Debug>(mut channel: &mut dyn Channel<Error = E>) -> Result<!, Error<E>> {
    loop {
        let msg: Vec<u8> = de::from_reader(&mut channel).map_err(Error::De)?;
        ser::into_writer(&msg, &mut channel).map_err(Error::Ser)?;
    }
}
