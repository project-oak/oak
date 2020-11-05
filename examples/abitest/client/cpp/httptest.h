/*
 * Copyright 2020 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef EXAMPLES_ABITEST_CLIENT_HTTPTEST_H
#define EXAMPLES_ABITEST_CLIENT_HTTPTEST_H

#include <map>
#include <string>

// Test functions return true on success, false on failure.
typedef bool (*HttpTestFn)();
extern const std::map<std::string, HttpTestFn> http_tests;

bool test_https_with_json_label_ok();
bool test_https_with_protobuf_label_and_identity_ok();
bool test_https_without_label_err_bad_request();
bool test_unsecure_http_err();

#endif  // EXAMPLES_ABITEST_CLIENT_HTTPTEST_H
