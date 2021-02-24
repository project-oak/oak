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

use crate::Report;
use assert_matches::assert_matches;

const TEST_TEE_MEASUREMENT: &str = "Test TEE measurement";
const TEST_TEE_DATA: &str = "Test TEE data";

#[test]
fn test_report_serialization() {
    let report = Report::new(TEST_TEE_MEASUREMENT.as_bytes(), TEST_TEE_DATA.as_bytes());

    let serialized_report_result = report.to_string();
    assert_matches!(serialized_report_result, Ok(_));
    let serialized_report = serialized_report_result.unwrap();

    let deserialized_report_result = Report::from_string(&serialized_report);
    assert_matches!(deserialized_report_result, Ok(_));
    let deserialized_report = deserialized_report_result.unwrap();

    assert_eq!(report, deserialized_report);
}
