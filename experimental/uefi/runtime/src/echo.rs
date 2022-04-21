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

use alloc::string::String;
use ciborium::{de, ser};

#[derive(Debug)]
pub enum Error<T> {
    // An error occured while deserializing.
    De(ciborium::de::Error<T>),

    // An error occured while serializing.
    Ser(ciborium::ser::Error<T>),
}

// Echoes all input on the interface back out.
pub fn echo<I, E>(mut interface: I) -> Result<!, Error<E>> where
   E: core::fmt::Debug,
   I: ciborium_io::Write<Error = E>,
   I: ciborium_io::Read<Error = E>  {
    loop {
        let msg: String = de::from_reader(&mut interface).map_err(Error::De)?;
        ser::into_writer(&msg, &mut interface).map_err(Error::Ser)?;
    }
}