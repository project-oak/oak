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

#![no_main]
#![feature(async_closure)]

use libfuzzer_sys::{
    arbitrary::{Arbitrary, Result, Unstructured},
    fuzz_target,
};
use oak_functions_abi::{Response, StatusCode};

#[derive(Debug)]
struct ResponseAndValidPolicy {
    response: Response,
    constant_response_size_bytes: usize,
}

impl Arbitrary<'_> for ResponseAndValidPolicy {
    fn arbitrary(raw: &mut Unstructured<'_>) -> Result<Self> {
        let body = <Vec<u8>>::arbitrary(raw)?;
        let status = {
            let status_code_as_u32: u32 =
                raw.int_in_range(0..=StatusCode::InternalServerError as u32)?;
            StatusCode::from_repr(status_code_as_u32).unwrap()
        };
        let body_len = body.len();
        let response = Response::create(status, body);

        // We limit the fuzzing to constant response size larger than the body.
        let constant_response_size_bytes = body_len + raw.int_in_range(0..=1000000)?;

        Ok(ResponseAndValidPolicy {
            response,
            constant_response_size_bytes,
        })
    }
}

// This fuzz target checks that the constant size policy applies to an arbitrary request.
fuzz_target!(|data: ResponseAndValidPolicy| {
    let constant_response_size_bytes = data.constant_response_size_bytes;
    let response = data
        .response
        .pad(constant_response_size_bytes)
        .unwrap()
        .encode_to_vec();

    // Check the response size, which is the constant response size plus a fixed offset, where the
    // status code and actual length are stored.
    assert_eq!(
        response.len(),
        oak_functions_abi::RESPONSE_BODY_OFFSET + constant_response_size_bytes
    )
});
