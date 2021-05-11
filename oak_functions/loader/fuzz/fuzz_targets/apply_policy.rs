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

use libfuzzer_sys::{
    arbitrary::{Arbitrary, Result, Unstructured},
    fuzz_target,
};
use oak_functions_abi::proto::{Response, StatusCode};
use oak_functions_loader::server::{apply_policy, Policy};

#[derive(Debug)]
struct ResponseAndValidPolicy {
    response: Response,
    policy: Policy,
}

impl Arbitrary<'_> for ResponseAndValidPolicy {
    fn arbitrary(raw: &mut Unstructured<'_>) -> Result<Self> {
        let body = <Vec<u8>>::arbitrary(raw)?;
        let status: i32 = raw.int_in_range(0..=StatusCode::InternalServerError as i32)?;
        let length = body.len() as u64;

        let response = Response {
            status,
            body,
            length,
        };

        // Instantiate a random valid policy.
        let policy = Policy {
            constant_response_size_bytes: raw.int_in_range(50..=5000)?,
            constant_processing_time: std::time::Duration::from_millis(10),
        };

        Ok(ResponseAndValidPolicy { response, policy })
    }
}

fuzz_target!(|data: ResponseAndValidPolicy| {
    let policy = data.policy;
    let function = move || handle_request(data.response);
    let response = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
        .block_on(apply_policy(policy, function))
        .unwrap();

    // Check the response size
    assert_eq!(response.body.len(), policy.constant_response_size_bytes)
});

// async closures are unstable, instead this function is used to return a future
async fn handle_request(response: Response) -> anyhow::Result<Response> {
    Ok(response)
}
