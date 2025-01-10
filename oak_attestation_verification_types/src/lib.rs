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

pub static AMD_SEV_SNP_PLATFORM_ENDORSEMENT_ID: [u8; 16] =
    [90, 18, 208, 15, 72, 160, 66, 36, 191, 244, 151, 92, 118, 87, 67, 143];
pub static FIRMWARE_ENDORSEMENT_ID: [u8; 16] =
    [222, 74, 13, 85, 96, 234, 77, 198, 171, 209, 9, 237, 116, 79, 128, 234];
pub static KERNEL_ENDORSEMENT_ID: [u8; 16] =
    [137, 81, 29, 101, 93, 53, 70, 1, 144, 11, 30, 109, 186, 248, 66, 182];
pub static SYSTEM_ENDORSEMENT_ID: [u8; 16] =
    [71, 34, 101, 93, 150, 61, 79, 201, 132, 67, 241, 69, 113, 221, 50, 162];
pub static APPLICATION_ENDORSEMENT_ID: [u8; 16] =
    [232, 78, 215, 20, 102, 157, 67, 10, 166, 15, 138, 101, 30, 90, 85, 3];
pub static CONTAINER_ENDORSEMENT_ID: [u8; 16] =
    [114, 151, 165, 31, 160, 93, 73, 161, 175, 219, 100, 205, 238, 7, 134, 45];
