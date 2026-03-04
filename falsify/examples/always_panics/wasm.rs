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

//! Wasm module that always panics. Used to test that the runner correctly
//! reports an error (inconclusive) status when a claim traps.

use falsify_wasm_sdk::{Claim, Evaluation};

struct AlwaysPanics;

impl Claim for AlwaysPanics {
    fn evaluate(&self, _input: &[u8]) -> Result<Evaluation, Box<dyn core::error::Error>> {
        panic!("this claim always panics");
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn main() {
    falsify_wasm_sdk::run(&AlwaysPanics);
}
