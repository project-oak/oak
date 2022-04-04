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

//! Oak Functions ABI Test for TF.

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    // Read the input_vector from the request.
    let input_vector = oak_functions::read_request().expect("Fail to read request body.");

    let result = oak_functions::oak_functions::tf_model_infer(input_vector);
    assert!(result.is_ok());

    // TODO(mschett): Add expected request.
    let response_body = todo!();
    oak_functions::write_response(response_body.as_bytes()).expect("Fail to write response body.");
}
