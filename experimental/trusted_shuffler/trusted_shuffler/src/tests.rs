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

use crate::{RequestHandler, TrustedShuffler};
use async_trait::async_trait;
use futures::future::join_all;
use std::{sync::Arc, time::Duration};
use tokio::{pin, time::sleep};

struct TestRequestHandler;

#[async_trait]
impl RequestHandler for TestRequestHandler {
    // A test function that processes requests.
    // In the real use-case, this function should send requests to the backend and
    // return responses.
    async fn handle(&self, request: Vec<u8>) -> anyhow::Result<Vec<u8>> {
        Ok(generate_response(request))
    }
}

// Non-async version of the `handle_request` function used to create expected responses.
fn generate_response(request: Vec<u8>) -> Vec<u8> {
    let parsed_request = String::from_utf8(request).expect("Couldn't parse request");
    format!("Response for: {}", parsed_request).into_bytes()
}

// Generates a request and a corresponding response from a string.
fn generate_request_and_expected_response(data: &str) -> (Vec<u8>, Vec<u8>) {
    let request = format!("Request: {}", data).into_bytes();
    let expected_response = generate_response(request.clone());
    (request, expected_response)
}

// Generates a test Trusted Shuffler with no timeout.
fn test_trusted_shuffler(k: usize) -> Arc<TrustedShuffler> {
    Arc::new(TrustedShuffler::new(
        k,
        None,
        Arc::new(TestRequestHandler {}),
    ))
}

#[tokio::test]
async fn anonymity_value_2_test() {
    let anonymity_value = 2;
    let trusted_shuffler = test_trusted_shuffler(anonymity_value);

    let (request, expected_response) = generate_request_and_expected_response("Test");
    let (background_request, expected_background_response) =
        generate_request_and_expected_response("Background test");

    let trusted_shuffler_clone = trusted_shuffler.clone();
    let background_result =
        tokio::spawn(async move { trusted_shuffler_clone.invoke(background_request).await });

    let response = trusted_shuffler.invoke(request.clone()).await;
    assert!(response.is_ok());
    assert_eq!(expected_response, response.unwrap());

    let background_result = background_result.await;
    assert!(background_result.is_ok());
    let background_response = background_result.unwrap();
    assert!(background_response.is_ok());
    assert_eq!(expected_background_response, background_response.unwrap());
}

#[tokio::test]
async fn anonymity_value_10_test() {
    let anonymity_value = 10;
    let trusted_shuffler = test_trusted_shuffler(anonymity_value);

    let (requests, expected_responses): (Vec<Vec<u8>>, Vec<Vec<u8>>) = (0..anonymity_value)
        .collect::<Vec<_>>()
        .iter()
        .map(|k| generate_request_and_expected_response(&format!("Test {}", k)))
        .unzip();

    let mut result_futures = vec![];
    for request in requests.iter() {
        let trusted_shuffler_clone = trusted_shuffler.clone();
        let request_clone = request.clone();
        let result_future =
            tokio::spawn(async move { trusted_shuffler_clone.invoke(request_clone).await });
        result_futures.push(result_future);
    }
    let results = join_all(result_futures).await;

    for (expected_response, result) in expected_responses.iter().zip(results.iter()) {
        assert!(result.is_ok());
        let response = result.as_ref().unwrap();
        assert!(response.is_ok());
        assert_eq!(*expected_response, *response.as_ref().unwrap());
    }
}

// Test that the Trusted Shuffler with the anonymity value equal to 3 waits for the 3rd client and
// doesn't process requests from only 2 clients.
#[tokio::test]
async fn waiting_for_enough_requests_test() {
    let anonymity_value = 3;
    let trusted_shuffler = test_trusted_shuffler(anonymity_value);

    let (request_1, _) = generate_request_and_expected_response("Test 1");
    let (request_2, expected_response) = generate_request_and_expected_response("Test 2");

    let trusted_shuffler_clone = trusted_shuffler.clone();
    tokio::spawn(async move { trusted_shuffler_clone.invoke(request_1).await });

    let response_future = trusted_shuffler.invoke(request_2);

    // Assert that after 200 ms no response for request_2 was received.
    pin!(response_future); // Pin to check it will be received after anonymity value is reached.
    let slept = tokio::select! {
        _ = sleep(Duration::from_millis(200)) => { true },
        _ = &mut response_future => { false }
    };
    assert!(slept);

    // Assert that after the third request was sent, request 2 is received.
    let (request_3, _) = generate_request_and_expected_response("Test 3");
    let trusted_shuffler_clone = trusted_shuffler.clone();
    tokio::spawn(async move { trusted_shuffler_clone.invoke(request_3).await });

    let result = response_future.await;
    assert!(result.is_ok());
    let response = result.unwrap();
    assert_eq!(expected_response, response);
}
