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

#![feature(async_closure)]
// Required by https://doc.rust-lang.org/std/cmp/trait.Ord.html#method.clamp
#![feature(clamp)]

pub mod proto {
    tonic::include_proto!("oak.functions.server");
}

pub mod attestation;
pub mod grpc;
pub mod logger;
pub mod lookup;
pub mod metrics;
pub mod server;
#[cfg(feature = "oak-tf")]
pub mod tf;
