//
// Copyright 2026 The Project Oak Authors
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

// Prost generated code cannot build on its own: it needs to be
// included into a manually crafted module structure. With crypto_rust_prost,
// this is not needed.

// TODO: b/333064338 - Remove this crate once we've stopped using cargo.

#![cfg_attr(not(feature = "std"), no_std)]
#![feature(never_type)]

macro_rules! include_proto {
    ($package: tt) => {
        include!(concat!(env!("OUT_DIR"), concat!("/", $package, ".rs")));
    };
}

pub mod oak {
    pub mod benchmark {
        include_proto!("oak.benchmark");
    }
}
