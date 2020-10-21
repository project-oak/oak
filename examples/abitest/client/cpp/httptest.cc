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

// Simple manual test case registry.
const std::map<std::string, HttpTestFn> http_tests = {
    // {"HttpsWithJsonLabelOk", test_https_with_json_label_ok},
    {"HttpsWithProtobufLabelAndIdentityOk", test_https_with_protobuf_label_and_identity_ok},
    // {"HttpsWithoutLabelErrBadRequest", test_https_without_label_err_bad_request},
    // {"UnsecureHttpErr", test_unsecure_http_err},
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
  std::string label_str = label.SerializeAsString();

  // unsigned char SIGNED_HASH_BYTES[] = {
  //     174, 145, 85,  83,  243, 64,  32,  49,  58,  219, 248, 105, 19,  64,  204, 161,
  //     178, 236, 0,   159, 173, 12,  179, 64,  78,  3,   203, 105, 127, 15,  108, 222,
  //     175, 209, 119, 128, 9,   208, 141, 178, 146, 244, 97,  141, 80,  127, 43,  201,
  //     55,  105, 170, 221, 157, 161, 224, 149, 160, 75,  249, 85,  144, 199, 7,   2};
  // unsigned char PUBLIC_KEY_BYTES[] = {201, 51,  138, 230, 147, 250, 75,  87,  155, 20,  151,
  //                                     142, 132, 31,  10,  83,  16,  88,  219, 221, 216, 108,
  //                                     26,  63,  77,  110, 97,  215, 253, 84,  116, 163};

  // const char* signed_hash = reinterpret_cast<const char*>(SIGNED_HASH_BYTES);
  // const char* public_key = reinterpret_cast<const char*>(PUBLIC_KEY_BYTES);

  std::string signed_hash_base64 =
      "rpFVU/NAIDE62/hpE0DMobLsAJ+tDLNATgPLaX8PbN6v0XeACdCNspL0YY1QfyvJN2mq3Z2h4JWgS/lVkMcHAg==";
  std::string public_key_base64 = "yTOK5pP6S1ebFJeOhB8KUxBY293YbBo/TW5h1/1UdKM=";

  oak::identity::SignedChallenge sig;
  sig.set_base64_signed_hash(signed_hash_base64);
  sig.set_base64_public_key(public_key_base64);
  LOG(INFO) << "@@@@@@@@@@ Created signautre";
  std::string sig_str = sig.SerializeAsString();
  LOG(INFO) << "@@@@@@@@@@ Serialized signautre";

  httplib::SSLClient cli("localhost", PORT);
  cli.set_ca_cert_path(CA_CERT_PATH);
  cli.enable_server_certificate_verification(true);
  httplib::Headers headers = {{"oak-label-bin", label_str},
                              {"oak-signed-auth-challenge-bin", sig_str}};

  auto res = cli.Get("/", headers);
  LOG(INFO) << "@@@@@@@@@@ Got result: " << res->status;
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
