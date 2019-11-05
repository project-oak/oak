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

extern crate abitest_backend;
extern crate abitest_frontend;
#[macro_use]
extern crate log;
extern crate oak;
extern crate protobuf;

use protobuf::ProtobufEnum;

#[cfg(test)]
#[macro_use]
extern crate assert_matches;
#[cfg(test)]
extern crate oak_tests;
#[cfg(test)]
extern crate serial_test;
#[cfg(test)]
#[macro_use]
extern crate serial_test_derive;

#[cfg(test)]
mod tests;

#[no_mangle]
pub extern "C" fn oak_main() -> i32 {
    error!("Dummy oak_main invoked");
    oak::OakStatus::ERR_TERMINATED.value()
}
