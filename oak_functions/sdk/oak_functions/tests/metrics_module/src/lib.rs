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

//! Oak Functions ABI Test for Metrics.

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    // Keep in sync with test_report_metric.
    let label = "a";
    // Some randomly chosen fixed value to report.
    let value = 42;

    let result = oak_functions::report_metric(label, value);
    assert!(result.is_ok());

    // Keep in sync with test_report_metric.
    let response_body = "MetricReported";
    oak_functions::write_response(response_body.as_bytes()).expect("Fail to write response body.");
}
