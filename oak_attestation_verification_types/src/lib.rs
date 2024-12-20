//
// Copyright 2024 The Project Oak Authors
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

#![no_std]
#![feature(trait_alias)]

extern crate alloc;

pub mod policy;
pub mod util;
pub mod verifier;

// IDs are generated as UUID v4 which is represented as a random string, except
// for the four bits that are used to indicate version 4 and two to three bits
// are used to indicate the variant.
// <https://datatracker.ietf.org/doc/rfc9562/>
pub static AMD_SEV_SNP_PLATFORM_ENDORSEMENT_ID: &[u8] = b"5a12d00f-48a0-4224-bff4-975c7657438f";
pub static FIRMWARE_ENDORSEMENT_ID: &[u8] = b"de4a0d55-60ea-4dc6-abd1-09ed744f80ea";
pub static KERNEL_ENDORSEMENT_ID: &[u8] = b"89511d65-5d35-4601-900b-1e6dbaf842b6";
pub static SYSTEM_ENDORSEMENT_ID: &[u8] = b"4722655d-963d-4fc9-8443-f14571dd32a2";
pub static APPLICATION_ENDORSEMENT_ID: &[u8] = b"e84ed714-669d-430a-a60f-8a651e5a5503";
pub static CONTAINER_ENDORSEMENT_ID: &[u8] = b"7297a51f-a05d-49a1-afdb-64cdee07862d";
