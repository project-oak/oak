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

//! Oak Functions differentially private metrics example.

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    let request = oak_functions::read_request().expect("Couldn't read request body.");
    if request == b"a" {
        oak_functions::report_event("a").expect("Couldn't report event.");
    }
}
