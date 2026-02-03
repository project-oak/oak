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

// Make libm implementations available to the linker.
// The Rust compiler-builtins only does this for UEFI targets, not bare-metal.
// See https://github.com/rust-lang/compiler-builtins/blob/master/src/math.rs#L23

#[unsafe(no_mangle)]
pub extern "C" fn fmod(a: f64, b: f64) -> f64 {
    libm::fmod(a, b)
}

#[unsafe(no_mangle)]
pub extern "C" fn fmodf(a: f32, b: f32) -> f32 {
    libm::fmodf(a, b)
}
