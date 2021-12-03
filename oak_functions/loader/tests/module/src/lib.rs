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
                "ConsistentLookup" => Self::test_consistent_lookup as TestFn,
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
            .ok_or(anyhow!("Couldn't find test: {}", &test_name))?;
        test(&test_name);
        Ok(())
    }

    fn test_consistent_lookup(key: &str) {
        let value = oak_functions::storage_get_item(key.as_bytes());
        assert_matches!(value, Ok(_));
        let value = value.unwrap();
        assert_matches!(value, Some(_));

        oak_functions::write_response(&value.unwrap()).expect("Failed to write response.");
    }
}

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    let test_manager = TestManager::new();
    test_manager.run_test().expect("Couldn't run test");
}
