//
// Copyright 2019 The Project Oak Authors
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

//! Functionality to allow use of the
//! [rand](https://rust-random.github.io/rand/rand/index.html) crate in Oak.

use rand_core::{impls, CryptoRng, Error, RngCore};

#[derive(Clone, Debug)]
pub struct OakRng;

impl RngCore for OakRng {
    fn next_u32(&mut self) -> u32 {
        impls::next_u32_via_fill(self)
    }

    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_fill(self)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.try_fill_bytes(dest).unwrap();
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        match crate::random_get(dest) {
            crate::OakStatus::OK => Ok(()),
            err => Err(Error::new(crate::io::error_from_nonok_status(err))),
        }
    }
}

// Assume the TCB is providing cryptographically secure randomness.
impl CryptoRng for OakRng {}
