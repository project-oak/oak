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

//! CTF SHA-2 arbiter binary.
//!
//! Thin entry point that delegates to `ctf_sha2::Arbiter`.

use clap::Parser;

fn main() {
    env_logger::init();
    falsify_native::falsify(falsify_native::FalsifyArgs::parse(), &ctf_sha2::Arbiter);
}
