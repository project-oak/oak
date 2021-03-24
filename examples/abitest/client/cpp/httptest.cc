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

#include "absl/strings/escaping.h"
#include "glog/logging.h"
#include "httplib_config.h"
#include "oak_abi/proto/identity.pb.h"
#include "oak_abi/proto/label.pb.h"

const char* CA_CERT_PATH = "../../../../../../../../../examples/certs/local/ca.pem";
const int PORT = 8383;

// Generated using the command:
//
// ```shell
// cargo run --manifest-path=oak_sign/Cargo.toml -- \
//     generate \
//     --private-key=http-test.key \
//     --public-key=http-test.pub
// ```
const char* PUBLIC_KEY_BASE64 = "MCowBQYDK2VwAyEAmSeVNkzZtyQ3v4ibhsdetuOW7j+pIQDK4UJxSEfngMM=";

// Generated using the command:
//
// ```shell
// cargo run --manifest-path=oak_sign/Cargo.toml -- \
//     sign \
//     --private-key=http-test.key \
//     --input-string="oak-challenge" \
//     --signature-file=http-test.sign
// ```
const char* SIGNED_HASH_BASE64 =
    "0OSnT9/FwnkuLN33yPQIPQaYbQJZGNxxFv3H/5lNdBy5d+IqS72C0MImora1QVAlrQ/AxldIfsQIJzW+LMT1CQ==";

// Simple manual test case registry.
const std::map<std::string, HttpTestFn> http_tests = {
    {"HttpsWithJsonLabelOk", test_https_with_json_label_ok},
    {"HttpsWithProtobufLabelAndIdentityOk", test_https_with_protobuf_label_and_identity_ok},
    {"HttpsWithoutLabelErrBadRequest", test_https_without_label_err_bad_request},
    {"UnsecureHttpErr", test_unsecure_http_err},
};

bool test_https_with_json_label_ok() {
  httplib::SSLClient cli("localhost", PORT);
  cli.set_ca_cert_path(CA_CERT_PATH);
  cli.enable_server_certificate_verification(true);
  httplib::Headers headers = {{"oak-label", "{\"confidentialityTags\":[],\"integrityTags\":[]}"}};

  auto res = cli.Get("/", headers);
  return res && res->status == 200;
}

bool test_https_with_protobuf_label_and_identity_ok() {
  oak::label::Label label;
  std::string label_str = absl::Base64Escape(label.SerializeAsString());

  std::string signed_hash;
  if (!absl::Base64Unescape(SIGNED_HASH_BASE64, &signed_hash)) {
    LOG(FATAL) << "Failed to decode base64 signed challenge";
  }
  std::string public_key;
  if (!absl::Base64Unescape(PUBLIC_KEY_BASE64, &public_key)) {
    LOG(FATAL) << "Failed to decode base64 public key";
  }

  oak::identity::SignedChallenge signature;
  signature.set_signed_hash(signed_hash);
  signature.set_public_key(public_key);
  std::string base64_proto_signature = absl::Base64Escape(signature.SerializeAsString());

  httplib::SSLClient cli("localhost", PORT);
  cli.set_ca_cert_path(CA_CERT_PATH);
  cli.enable_server_certificate_verification(true);
  httplib::Headers headers = {{"oak-label-bin", label_str},
                              {"oak-signed-auth-challenge-bin", base64_proto_signature}};

  auto res = cli.Get("/", headers);
  return res && res->status == 200;
}

bool test_https_without_label_err_bad_request() {
  httplib::SSLClient cli("localhost", PORT);
  cli.set_ca_cert_path(CA_CERT_PATH);
  cli.enable_server_certificate_verification(true);

  auto res = cli.Get("/");
  return res && res->status == 400;
}

bool test_unsecure_http_err() {
  httplib::Client cli("localhost", PORT);
  httplib::Headers headers = {{"oak-label", "{\"confidentialityTags\":[],\"integrityTags\":[]}"}};

  auto res = cli.Get("/", headers);
  // The server should reject the request, since the request is not being sent over a TLS
  // connection.
  return !res;
}
