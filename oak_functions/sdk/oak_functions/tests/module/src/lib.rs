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

use anyhow::{anyhow, Context};
use assert_matches::assert_matches;
use maplit::hashmap;
use std::collections::HashMap;

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
            ],
        }
    }

    fn run_test(&self) -> anyhow::Result<()> {
        let request = oak_functions::read_request()
            .map_err(|error| anyhow!("Couldn't read request: {:?}", error))?;
        let test_name = String::from_utf8(request).context("Couldn't parse request")?;
        let test = self
            .tests
            .get(&test_name as &str)
            .ok_or_else(|| anyhow!("Couldn't find test: {}", &test_name))?;
        test(&test_name);
        Ok(())
    }

    fn test_read_write(_request: &str) {
        let result = oak_functions::write_response(b"ReadWriteResponse");
        assert_matches!(result, Ok(_));
    }

    /// Tests that a second call to [`oak_functions_abi::read_request`] returns the same value.
    fn test_double_read(first_request_body: &str) {
        let second_read_request =
            oak_functions::read_request().expect("Failed to read second request.");
        assert_eq!(second_read_request, first_request_body.as_bytes());
        // If assert_eq fails then run_test will return with an empty response body.
        oak_functions::write_response(b"DoubleReadResponse").expect("Failed to write response.")
    }

    /// Tests that multiple calls to [`oak_functions_abi::write_response`] will replace the earlier
    /// responses. The response body has to be checked in the integration test.
    fn test_double_write(_request: &str) {
        // First response contains a different value.
        oak_functions::write_response(b"FirstResponseInDoubleWrite")
            .expect("Failed to write first response.");
        oak_functions::write_response(b"DoubleWriteResponse")
            .expect("Failed to write second response.");
    }

    // TODO(#2417): Test logging of `write_log_message`
    fn test_write_log(request: &str) {
        let result = oak_functions::write_log_message(request);
        assert_matches!(result, Ok(_));
        let result = oak_functions::write_response(b"WriteLogResponse");
        assert_matches!(result, Ok(_));
    }

    /// Tests [`oak_functions_abi::storage_get_item`] when the key in the lookup data. The lookup
    /// data is set in the integration test. The value has to be checked in the integration
    /// test.
    // TODO(#2414): Add test for ERR_STORAGE_ITEM_NOT_FOUND
    fn test_storage_get(key: &str) {
        let value = oak_functions::storage_get_item(key.as_bytes());
        assert_matches!(value, Ok(_));
        let value = value.unwrap();
        assert_matches!(value, Some(_));

        oak_functions::write_response(&value.unwrap()).expect("Failed to write response.");
    }

    // TODO(#2415): Add tests for report_metric.

    // TODO(#2416): Add tests for tf_model_infer.
}

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    let test_manager = TestManager::new();
    test_manager.run_test().expect("Couldn't run test");
}
