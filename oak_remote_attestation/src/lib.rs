//
// Copyright 2021 The Project Oak Authors
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

//! A library for clients and servers to implement Remote Attestation as described
//! [here](https://github.com/project-oak/oak/blob/main/docs/remote-attestation.md).

#![no_std]

extern crate alloc;

pub mod crypto;
pub mod handshaker;
pub mod message;
#[cfg(test)]
mod tests;
