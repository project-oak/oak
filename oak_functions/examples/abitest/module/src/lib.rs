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
use oak_functions_abitest_common::*;
use std::collections::HashMap;

type TestFn = fn(&str) -> anyhow::Result<()>;

struct TestManager {
    tests: HashMap<String, TestFn>,
}

impl TestManager {
    fn new() -> Self {
        let mut tests = HashMap::new();
        tests.insert(TEST_READ_WRITE.to_string(), Self::test_read_write as TestFn);
        tests.insert(
            TEST_DOUBLE_READ.to_string(),
            Self::test_double_read as TestFn,
        );
        tests.insert(
            TEST_DOUBLE_WRITE.to_string(),
            Self::test_double_write as TestFn,
        );
        tests.insert(TEST_WRITE_LOG.to_string(), Self::test_write_log as TestFn);
        tests.insert(
            TEST_STORAGE_GET.to_string(),
            Self::test_storage_get as TestFn,
        );

        Self { tests }
    }

    fn run_test(&self) -> anyhow::Result<()> {
        let request = oak_functions::read_request()
            .map_err(|error| anyhow!("Couldn't read request: {:?}", error))?;
        let test_name = String::from_utf8(request).context("Couldn't parse request")?;
        let test = self
            .tests
            .get(&test_name)
            .ok_or(anyhow!("Couldn't find test: {}", &test_name))?;
        test(&test_name).context(format!("Couldn't run test: {}", &test_name))
    }

    fn test_read_write(_request: &str) -> anyhow::Result<()> {
        let result = oak_functions::write_response(TEST_READ_WRITE_RESPONSE.as_bytes());
        assert_matches!(result, Ok(_));
        Ok(())
    }

    /// Tests that a second call to [`oak_functions_abi::read_request`] returns the same value.
    fn test_double_read(request: &str) -> anyhow::Result<()> {
        let result = oak_functions::read_request();
        assert_matches!(result, Ok(_));
        let second_read_result = result.unwrap();
        assert_eq!(second_read_result, request.as_bytes());

        let result = oak_functions::write_response(TEST_DOUBLE_READ_RESPONSE.as_bytes());
        assert_matches!(result, Ok(_));
        Ok(())
    }

    /// Tests that multiple calls to [`oak_functions_abi::write_response`] will replace the earlier
    /// responses. Response value is checked on the client side.
    fn test_double_write(_request: &str) -> anyhow::Result<()> {
        // First response is empty.
        let result = oak_functions::write_response("".as_bytes());
        assert_matches!(result, Ok(_));

        let result = oak_functions::write_response(TEST_DOUBLE_WRITE_RESPONSE.as_bytes());
        assert_matches!(result, Ok(_));
        Ok(())
    }

    fn test_write_log(request: &str) -> anyhow::Result<()> {
        let result = oak_functions::write_log_message(request);
        assert_matches!(result, Ok(_));
        let result = oak_functions::write_response(TEST_WRITE_LOG_RESPONSE.as_bytes());
        assert_matches!(result, Ok(_));
        Ok(())
    }

    /// Tests the correctness of the data retrieved from the database.
    /// Response value is checked on the client side.
    fn test_storage_get(request: &str) -> anyhow::Result<()> {
        let result = oak_functions::storage_get_item(request.as_bytes());
        assert_matches!(result, Ok(_));
        let data = result.unwrap();
        assert_matches!(data, Some(_));

        let result = oak_functions::write_response(&data.unwrap());
        assert_matches!(result, Ok(_));
        Ok(())
    }
}

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    let test_manager = TestManager::new();
    test_manager.run_test().expect("Couldn't run test");
}
