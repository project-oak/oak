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

//! Oak Functions ABI test.

#![feature(assert_matches)]

use core::assert_matches::assert_matches;
use std::collections::HashMap;

use anyhow::anyhow;
use maplit::hashmap;

type TestFn = fn(&str) -> ();

struct TestManager<'a> {
    tests: HashMap<&'a str, TestFn>,
}

impl TestManager<'static> {
    fn new() -> Self {
        Self {
            tests: hashmap! [
                "ReadWrite" => Self::test_read_write as TestFn,
                "DoubleRead" => Self::test_double_read as TestFn,
                "DoubleWrite" => Self::test_double_write as TestFn,
                "WriteLog" => Self::test_write_log as TestFn,
                "StorageGet" => Self::test_storage_get as TestFn,
                "StorageGetItemNotFound" => Self::test_storage_get_item_not_found as TestFn,
                "LargeKey" => Self::test_storage_get_item_huge_key as TestFn,
            ],
        }
    }

    fn run_test(&self) -> anyhow::Result<()> {
        let request = oak_functions_sdk::read_request()
            .map_err(|error| anyhow!("couldn't read request: {:?}", error))?;
        let test_name = String::from_utf8(request)
            .map_err(|err| anyhow::anyhow!("couldn't parse request: {err}"))?;
        let test = self
            .tests
            .get(&test_name as &str)
            .ok_or_else(|| anyhow!("couldn't find test: {}", &test_name))?;
        test(&test_name);
        Ok(())
    }

    fn test_read_write(_request: &str) {
        let result = oak_functions_sdk::write_response(b"ReadWriteResponse");
        assert_matches!(result, Ok(_));
    }

    /// Tests that a second call to [`oak_functions_sdk::read_request`] returns
    /// the same value.
    fn test_double_read(first_request_body: &str) {
        let second_read_request =
            oak_functions_sdk::read_request().expect("couldn't read second request");
        assert_eq!(second_read_request, first_request_body.as_bytes());
        // If assert_eq fails then run_test will return with an empty response body.
        oak_functions_sdk::write_response(b"DoubleReadResponse").expect("couldn't write response")
    }

    /// Tests that multiple calls to [`oak_functions_sdk::write_response`] will
    /// replace the earlier responses. The response body has to be checked
    /// in the integration test.
    fn test_double_write(_request: &str) {
        // First response contains a different value.
        oak_functions_sdk::write_response(b"FirstResponseInDoubleWrite")
            .expect("couldn't write first response");
        oak_functions_sdk::write_response(b"DoubleWriteResponse")
            .expect("couldn't write second response");
    }

    // TODO(#2417): Test logging of [`oak_functions_sdk::write_log_message`]
    fn test_write_log(request: &str) {
        let result = oak_functions_sdk::write_log_message(request);
        assert_matches!(result, Ok(_));
        let result = oak_functions_sdk::write_response(b"WriteLogResponse");
        assert_matches!(result, Ok(_));
    }

    /// Tests [`oak_functions_sdk::storage_get_item`] when the key is in the
    /// lookup data. The lookup data is set in the integration test. The
    /// value has to be checked in the integration test.
    fn test_storage_get(key: &str) {
        let value = oak_functions_sdk::storage_get_item(key.as_bytes());
        assert_matches!(value, Ok(_));
        let value = value.unwrap();
        assert_matches!(value, Some(_));

        oak_functions_sdk::write_response(&value.unwrap()).expect("couldn't write response");
    }

    /// Tests [`oak_functions_sdk::storage_get_item`] when the key is not in the
    /// lookup data. The lookup data is set in the integration test. When no
    /// value is found, [`oak_functions_sdk::storage_get_item`] returns
    /// None.
    fn test_storage_get_item_not_found(key: &str) {
        let value = oak_functions_sdk::storage_get_item(key.as_bytes());
        let response_msg = match value {
            Ok(None) => b"No item found".to_vec(),
            Ok(Some(mut value)) => {
                let mut msg = b"Unexpected item found: value: ".to_vec();
                msg.append(&mut value);
                msg
            }
            Err(_) => b"Unexpected error".to_vec(),
        };
        oak_functions_sdk::write_response(&response_msg).expect("couldn't write response")
    }

    /// Tests [`oak_functions_sdk::storage_get_item`] when the key is large. The
    /// lookup data is set in the integration test.
    fn test_storage_get_item_huge_key(_key: &str) {
        // Easier to ignore key from request, just create the same as in the integration
        // test.
        let key: Vec<u8> = vec![42u8; 1 << 20];
        let value = oak_functions_sdk::storage_get_item(&key)
            .expect("couldn't receive response")
            .expect("no value found");

        oak_functions_sdk::write_response(&value).expect("couldn't write response");
    }
}

#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn main() {
    let test_manager = TestManager::new();
    test_manager.run_test().expect("couldn't run test");
}
