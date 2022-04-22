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

use crate::TrustedShuffler;
use futures::future::join_all;
use std::{sync::Arc, time::Duration};
use tokio::time::timeout;

const TEST_ANONYMITY_VALUE: usize = 10;
const TEST_TIMEOUT_MILLISECONDS: u64 = 100;

async fn send_request(request: Vec<u8>) -> Vec<u8> {
    request
}

#[tokio::test]
async fn trusted_shuffler_test() {
    let trusted_shuffler = Arc::new(TrustedShuffler::new(2, send_request));

    let request = "Test request".to_string().as_bytes().to_vec();
    let background_request = "Test request background".to_string().as_bytes().to_vec();

    let trusted_shuffler_clone = trusted_shuffler.clone();
    let background_request_clone = background_request.clone();
    let background_result = tokio::spawn(async move {
        trusted_shuffler_clone
            .invoke(background_request_clone)
            .await
    });

    let response = trusted_shuffler.invoke(request.clone()).await;
    assert!(response.is_ok());
    assert_eq!(request, response.unwrap());

    let background_result = background_result.await;
    assert!(background_result.is_ok());
    let background_response = background_result.unwrap();
    assert!(background_response.is_ok());
    assert_eq!(background_request, background_response.unwrap());
}

#[tokio::test]
async fn trusted_shuffler_waiting_test() {
    let trusted_shuffler = Arc::new(TrustedShuffler::new(3, send_request));

    let request_1 = "Test request 1".to_string().as_bytes().to_vec();
    let request_2 = "Test request 2".to_string().as_bytes().to_vec();

    let trusted_shuffler_clone = trusted_shuffler.clone();
    tokio::spawn(async move { trusted_shuffler_clone.invoke(request_1).await });

    let response_future = trusted_shuffler.invoke(request_2);
    let result = timeout(
        Duration::from_millis(TEST_TIMEOUT_MILLISECONDS),
        response_future,
    )
    .await;
    assert!(result.is_err());
}

#[tokio::test]
async fn trusted_shuffler_background_test() {
    let trusted_shuffler = Arc::new(TrustedShuffler::new(TEST_ANONYMITY_VALUE, send_request));

    let requests: Vec<Vec<u8>> = (0..TEST_ANONYMITY_VALUE)
        .collect::<Vec<_>>()
        .iter()
        .map(|k| format!("Test request {}", k).as_bytes().to_vec())
        .collect();

    let mut result_futures = vec![];
    for request in requests.iter() {
        let trusted_shuffler_clone = trusted_shuffler.clone();
        let request_clone = request.clone();
        let result_future =
            tokio::spawn(async move { trusted_shuffler_clone.invoke(request_clone).await });
        result_futures.push(result_future);
    }
    let results = join_all(result_futures).await;

    for (request, result) in requests.iter().zip(results.iter()) {
        assert!(result.is_ok());
        let response = result.as_ref().unwrap();
        assert!(response.is_ok());
        assert_eq!(request.clone(), *response.as_ref().unwrap());
    }
}
