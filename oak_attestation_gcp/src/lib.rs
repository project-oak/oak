//
// Copyright 2025 The Project Oak Authors
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

#![feature(assert_matches)]
#![feature(box_patterns)]
#![feature(try_blocks)]

extern crate alloc;

pub mod attestation;
pub mod cosign;
pub mod jwt;
pub mod policy;
pub mod policy_generator;

pub const CONFIDENTIAL_SPACE_ROOT_CERT_PEM: &str =
    include_str!("../data/confidential_space_root.pem");

pub const OAK_SESSION_NOISE_V1_AUDIENCE: &str = "d9b8d46d-6841-4825-9b5e-e77768638044";
