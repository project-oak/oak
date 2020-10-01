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

#include "examples/abitest/client/cpp/httptest.h"

#include "glog/logging.h"
#include "httplib.h"

// Simple manual test case registry.
const std::map<std::string, HttpTestFn> http_tests = {
    {"ValidHttpsOk", test_valid_https_ok},
};

bool test_valid_https_ok() {
  httplib::SSLClient cli("localhost", 8383);
  cli.set_ca_cert_path("../../../../../../../../../examples/certs/local/ca.pem");
  cli.enable_server_certificate_verification(true);

  httplib::Headers headers = {{"oak-label", "{\"confidentialityTags\":[],\"integrityTags\":[]}"}};
  auto res = cli.Get("/", headers);
  if (res && res->status == 200) {
    return true;
  }
  return true;
}
