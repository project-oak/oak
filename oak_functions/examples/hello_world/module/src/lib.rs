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

//! Oak functions hello world example.
//!
//! To build and run manually:
//! 1. Build the wasm module:
//! ```shell
//! cargo -Zunstable-options build --release \
//!   --target=wasm32-unknown-unknown \
//!   --manifest-path=oak_functions/examples/hello_world/module/Cargo.toml \
//!   --out-dir=oak_functions/examples/hello_world/bin
//! ```
//!
//! 2. Build loader with debugging enabled if needed:
//!```shell
//! cargo build --manifest-path=./oak_functions/loader/Cargo.toml \
//!   --release
//!   --features=oak-unsafe
//! ```
//!
//! 3. Run the loader:
//!```shell
//! /oak_functions/loader/target/release/oak_functions_loader \
//!   --wasm-path=oak_functions/examples/hello_world/bin/hello_world.wasm
//! ```
//!
//! 4. Invoke:
//!```shell
//! curl --include --fail-early --request POST --data 'request-body' localhost:8080/invoke
//! ```

use oak_functions as sdk;

#[cfg(test)]
mod tests;

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    // A panic in the Rust module code cannot safely pass through the FFI
    // boundary, so catch any panics here and drop them.
    // https://doc.rust-lang.org/nomicon/ffi.html#ffi-and-panics
    let _ = ::std::panic::catch_unwind(|| {
        sdk::set_panic_hook();

        // Read the request
        let request_body = sdk::read_request_body().expect("Couldn't read request body.");

        // Write the response
        let response_body = format!(
            "Welcome to Oak functions!\nRequest length: {}.\n",
            request_body.len()
        );

        let _res = sdk::write_response_body(&response_body);
    });
}
