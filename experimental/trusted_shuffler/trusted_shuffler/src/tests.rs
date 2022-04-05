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

use crate::{AsyncQueue, RequestIdGenerator, TrustedShuffler};
use assert_matches::assert_matches;
use std::{collections::HashSet, sync::Arc};

const TEST_ANONYMITY_VALUE: usize = 10;
const CHANNEL_BUFFER_SIZE: usize = 100;

#[test]
fn test_id_generator() {
    let mut generator = RequestIdGenerator::new(TEST_ANONYMITY_VALUE);

    let mut request_id_set = HashSet::new();
    let mut batch_id_set = HashSet::new();
    for _ in 0..TEST_ANONYMITY_VALUE {
        let request_id = generator.generate();
        batch_id_set.insert(request_id.batch_id.clone());
        request_id_set.insert(request_id);
    }
    assert_eq!(request_id_set.len(), TEST_ANONYMITY_VALUE);
    assert_eq!(batch_id_set.len(), 1);

    let prev_batch_id = batch_id_set.iter().cloned().next().unwrap();
    let new_request_id = generator.generate();
    assert_ne!(prev_batch_id, new_request_id.batch_id);
}

// #[tokio::test]
// async fn async_queue_test() {
//     let test_values = vec![1, 2, 3, 4, 5];
//     let queue = Arc::new(AsyncQueue::new(CHANNEL_BUFFER_SIZE));

//     let cloned_test_values = test_values.clone();
//     let cloned_queue = queue.clone();
//     let background = test_utils::background(|_| async move {
//         for value in cloned_test_values.iter() {
//             cloned_queue.put(value.clone()).await;
//         }
//     });

//     for expected_value in test_values.iter() {
//         let value = queue.get().await;
//         assert!(value.is_ok());
//         assert_eq!(value.unwrap(), *expected_value);
//     }

//     background.terminate_and_join().await;
// }

#[tokio::test]
async fn trusted_shuffler_test() {
    let trusted_shuffler: TrustedShuffler<String, String> = TrustedShuffler::new(TEST_ANONYMITY_VALUE);
    // let trusted_shuffler_arc = Arc::new(trusted_shuffler);
    // let trusted_shuffler_arc_clone = trusted_shuffler_arc.clone();
    let trusted_shuffler_clone = trusted_shuffler.clone();

    let background = test_utils::background(|_| async move {
        // let trusted_shuffler_arc_clone = &mut *trusted_shuffler_arc_clone;
        // let request = trusted_shuffler_arc_clone.pop_request().await;
        let request = trusted_shuffler_clone.pop_request().await;
    });

    // trusted_shuffler_arc.invoke("Test request".to_string());
    trusted_shuffler.invoke("Test request".to_string());
}

// #[tokio::test]
// async fn test() {
//     let trusted_shuffler: TrustedShuffler<String, String> = TrustedShuffler::new(TEST_ANONYMITY_VALUE);
//     let trusted_shuffler_arc = Arc::new(trusted_shuffler);
//     let trusted_shuffler_arc_clone = trusted_shuffler_arc.clone();

//     let background = test_utils::background(|_| async move {
//         // let trusted_shuffler_arc_clone = &mut *trusted_shuffler_arc_clone;
//         // let request = trusted_shuffler_arc_clone.pop_request().await;
//         trusted_shuffler_arc_clone.generate();
//     });

//     // trusted_shuffler_arc.invoke("Test request".to_string());
//     trusted_shuffler_arc.generate();
// }
