//
// Copyright 2019 The Project Oak Authors
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

// Keep clippy from complaining about a needless call to `Default::default()`.
#[allow(clippy::needless_update)]
fn main() {
    oak_utils::compile_protos_with_options(
        &["../oak_abi/proto/oak_abi.proto"],
        &[".."],
        oak_utils::ProtoOptions {
            // Exclude generation of service code and HandleVisit auto-derive, as it would require a
            // reference to the `oak_io` crate to compile.
            generate_services: false,
            derive_handle_visit: false,
            ..Default::default()
        },
    );
}
