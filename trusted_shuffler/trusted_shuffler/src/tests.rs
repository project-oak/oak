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

use crate::{
    EncryptedRequest, EncryptedResponse, PlaintextRequest, PlaintextResponse, RequestHandler,
    TrustedShuffler,
};
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
    async fn handle(&self, request: PlaintextRequest) -> anyhow::Result<PlaintextResponse> {
        if drop_request(&request) {
            // In that case we don't send an answer ever.
            loop {
                tokio::task::yield_now().await;
            }
        }
        Ok(get_plaintext_response(&request))
    }
}

// Non-async version of the `handle_request` function used to create expected responses.
fn get_plaintext_response(request: &PlaintextRequest) -> PlaintextResponse {
    PlaintextResponse {
        headers: hyper::HeaderMap::new(),
        data: hyper::body::Bytes::from(request.body.clone()),
        trailers: hyper::HeaderMap::new(),
    }
}

// Non-async version of the `handle_request` function used to create expected responses.
fn get_encrypted_response(request: &EncryptedRequest) -> EncryptedResponse {
    EncryptedResponse {
        headers: hyper::HeaderMap::new(),
        data: hyper::body::Bytes::from(request.body.clone()),
        trailers: hyper::HeaderMap::new(),
    }
}

// Generates request which will be dropped by the test backend, because we indicate it has to be
// dropped in the request itself.
fn generate_dropped_request() -> EncryptedRequest {
    // "Drop" has to be consistent with [`drop_request`].
    let (dropped_request, _) = generate_secret_request_and_expected_response("Drop");
    dropped_request
}

// If true, then the test backend does not answer the request.
fn drop_request(request: &PlaintextRequest) -> bool {
    String::from_utf8(request.body.clone())
        .unwrap()
        .contains("Drop")
}

// Generates a request and a corresponding response from a string.
fn generate_secret_request_and_expected_response(
    data: &str,
) -> (EncryptedRequest, EncryptedResponse) {
    let request = EncryptedRequest {
        body: format!("Request: {}", data).into_bytes(),
        headers: hyper::HeaderMap::new(),
        uri: hyper::Uri::from_static("test.com"),
    };

    let expected_response = get_encrypted_response(&request);
    (request, expected_response)
}

// Generates a test Trusted Shuffler with no timeout.
fn test_trusted_shuffler(batch_size: usize) -> Arc<TrustedShuffler> {
    Arc::new(TrustedShuffler::new(
        batch_size,
        None,
        Arc::new(TestRequestHandler {}),
    ))
}

// Generates a test Trusted Shuffler with given timeout.
fn test_trusted_shuffler_with_timeout(
    batch_size: usize,
    timeout: Duration,
) -> Arc<TrustedShuffler> {
    Arc::new(TrustedShuffler::new(
        batch_size,
        Some(timeout),
        Arc::new(TestRequestHandler {}),
    ))
}

#[tokio::test]
async fn batch_size_2_test() {
    let batch_size = 2;
    let trusted_shuffler = test_trusted_shuffler(batch_size);

    let (request, expected_response) = generate_secret_request_and_expected_response("Test");
    let (background_request, expected_background_response) =
        generate_secret_request_and_expected_response("Background test");

    let trusted_shuffler_clone = trusted_shuffler.clone();
    let background_result =
        tokio::spawn(async move { trusted_shuffler_clone.invoke(background_request).await });

    let response = trusted_shuffler.invoke(request).await;
    assert!(response.is_ok());
    assert_eq!(expected_response, response.unwrap());

    let background_result = background_result.await;
    assert!(background_result.is_ok());
    let background_response = background_result.unwrap();
    assert!(background_response.is_ok());
    assert_eq!(expected_background_response, background_response.unwrap());
}

#[tokio::test]
async fn batch_size_10_test() {
    let batch_size = 10;
    let trusted_shuffler = test_trusted_shuffler(batch_size);

    let (requests, expected_responses): (Vec<EncryptedRequest>, Vec<EncryptedResponse>) = (0
        ..batch_size)
        .collect::<Vec<_>>()
        .iter()
        .map(|k| generate_secret_request_and_expected_response(&format!("Test {}", k)))
        .unzip();

    let mut result_futures = vec![];
    for request in requests.into_iter() {
        let trusted_shuffler_clone = trusted_shuffler.clone();
        let result_future =
            tokio::spawn(async move { trusted_shuffler_clone.invoke(request).await });
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
    let batch_size = 3;
    let trusted_shuffler = test_trusted_shuffler(batch_size);

    let (request_1, _) = generate_secret_request_and_expected_response("Test 1");
    let (request_2, expected_response) = generate_secret_request_and_expected_response("Test 2");

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
    let (request_3, _) = generate_secret_request_and_expected_response("Test 3");
    let trusted_shuffler_clone = trusted_shuffler.clone();
    tokio::spawn(async move { trusted_shuffler_clone.invoke(request_3).await });

    let result = response_future.await;
    assert!(result.is_ok());
    let response = result.unwrap();
    assert_eq!(expected_response, response);
}

// If one request receives no response from the backend after the given timeout, then the Trusted
// Shuffler responds with the empty response.
#[tokio::test]
async fn one_empty_response_test() {
    let batch_size = 2;
    // This should give the non-empty response enough time to arrive.
    let timeout = Duration::from_millis(200);
    let trusted_shuffler = test_trusted_shuffler_with_timeout(batch_size, timeout);

    let (request, expected_response) =
        generate_secret_request_and_expected_response("Request (not-dropped)");
    let dropped_request = generate_dropped_request();

    let trusted_shuffler_clone = trusted_shuffler.clone();
    let response = tokio::spawn(async move { trusted_shuffler_clone.invoke(request).await });

    // Send the dropped_request. The backend will not answer it, but the Trusted Shuffler will send
    // an empty response.
    let response_from_dropped = trusted_shuffler.invoke(dropped_request).await;
    assert_eq!(
        PlaintextResponse::empty().encrypt(),
        response_from_dropped.unwrap()
    );

    // The backend did answer the request and the Trusted Shuffler forwarded it.
    let response = response.await.unwrap();
    assert_eq!(expected_response, response.unwrap());
}

// If all requests receive a response from the backend within the given timeout, then the Trusted
// Shuffler responds with the all responses.
#[tokio::test]
async fn no_empty_response_test() {
    let batch_size = 2;
    // This should give the non-empty response enough time to arrive.
    let timeout = Duration::from_millis(200);
    let trusted_shuffler = test_trusted_shuffler_with_timeout(batch_size, timeout);

    let (request_1, expected_response_1) =
        generate_secret_request_and_expected_response("Request 1");
    let (request_2, expected_response_2) =
        generate_secret_request_and_expected_response("Request 2");

    let trusted_shuffler_clone = trusted_shuffler.clone();
    let response = tokio::spawn(async move { trusted_shuffler_clone.invoke(request_1).await });

    let response_2 = trusted_shuffler.invoke(request_2).await;
    assert_eq!(expected_response_2, response_2.unwrap());

    let response_1 = response.await.unwrap();
    assert_eq!(expected_response_1, response_1.unwrap());
}

// If no request receives a response from the backend within the given timeout, then the Trusted
// Shuffler responds with the all empty responses.
#[tokio::test]
async fn all_empty_responses_test() {
    let batch_size = 2;
    let timeout = Duration::from_millis(200);
    let trusted_shuffler = test_trusted_shuffler_with_timeout(batch_size, timeout);

    let dropped_request_1 = generate_dropped_request();
    let dropped_request_2 = generate_dropped_request();

    let trusted_shuffler_clone = trusted_shuffler.clone();
    let response =
        tokio::spawn(async move { trusted_shuffler_clone.invoke(dropped_request_1).await });

    let response_2 = trusted_shuffler.invoke(dropped_request_2).await;
    assert_eq!(PlaintextResponse::empty().encrypt(), response_2.unwrap());

    let response_1 = response.await.unwrap();
    assert_eq!(PlaintextResponse::empty().encrypt(), response_1.unwrap());
}
