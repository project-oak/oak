//
// Copyright 2020 The Project Oak Authors
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

use platforms::{platform::Platform, target::OS};

fn main() {
    // Define the platform specific rust targets for Rust clients and servers.
    // This is kept out of the main.rs so as to provide a generic porting
    // mechanism that does not require modification of the codebase in src.
    // These values are overriden by command line options to runner.
    let server_target;
    let client_target;
    match Platform::guess_current() {
        Some(current_platform) => {
            // Export the host target as a default for use by tsan
            println!("cargo:rustc-env=HOST_RUST_TARGET={}", current_platform);
            match current_platform.target_os {
                OS::MacOS => {
                    // macOS requires translation to -apple-darwin for Rust
                    server_target =
                        format!("{}{}{}", current_platform.target_arch, "-apple-", "darwin");
                    client_target =
                        format!("{}{}{}", current_platform.target_arch, "-apple-", "darwin");
                }

                // Any other OS: Currently this form assumes Linux. Other OS's may
                // also work with this target spec, however, it is expected that
                // for other OS support would modify this file as needed.
                OS::Linux => {
                    // The 'other OS' defaults are for musl and gnu
                    server_target = format!(
                        "{}{}{}{}",
                        current_platform.target_arch,
                        "-unknown-",
                        current_platform.target_os,
                        "-musl"
                    );
                    client_target = format!(
                        "{}{}{}{}",
                        current_platform.target_arch,
                        "-unknown-",
                        current_platform.target_os,
                        "-gnu"
                    );
                }
                _ => {
                    panic!(
                        "OS {} not supported for this project",
                        current_platform.target_os
                    );
                }
            }
        }
        None => panic!("Can't guess the current platform!"),
    }
    // Having converted the current target type, we now check if its a sane triple for Rust
    // by searchng for it.
    match Platform::find(&server_target) {
        Some(target) => println!("cargo:rustc-env=SERVER_RUST_TARGET={}", target),
        None => panic!("Server target {} is not recognised by Rust", &server_target),
    }
    match Platform::find(&client_target) {
        Some(target) => println!("cargo:rustc-env=CLIENT_RUST_TARGET={}", target),
        None => panic!("Client target {} is not recognised by Rust", &client_target),
    }
}
