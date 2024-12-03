/*
 * Copyright 2024 The Project Oak Authors
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

#include "cc/oak_session/oak_session_bindings.h"

#include <string>

#include "cc/oak_session/testing/matchers.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "proto/session/session.pb.h"

namespace oak::session {
namespace {

using ::oak::session::v1::SessionRequest;
using ::oak::session::v1::SessionResponse;
using ::testing::Eq;

void DoHandshake(ServerSession* server_session, ClientSession* client_session) {
  ErrorOrBytes init = client_get_outgoing_message(client_session);
  ASSERT_THAT(init, IsResult());

  // We could just past init.result directly, but let's ensure that the request
  // successfully goes through the ser/deser properly.
  SessionRequest request;
  ASSERT_TRUE(
      request.ParseFromString(oak::session::BytesToString(*init.result)));
  std::string request_reserialized;
  ASSERT_TRUE(request.SerializeToString(&request_reserialized));
  Bytes request_bytes = oak::session::BytesFromString(request_reserialized);
  free_bytes(init.result);

  ASSERT_THAT(server_put_incoming_message(server_session, request_bytes),
              NoError());

  ErrorOrBytes init_resp = server_get_outgoing_message(server_session);
  ASSERT_THAT(init_resp, IsResult());

  SessionResponse response;
  ASSERT_TRUE(
      response.ParseFromString(oak::session::BytesToString(*init_resp.result)));
  free_bytes(init_resp.result);
  std::string response_reserialized;
  ASSERT_TRUE(response.SerializeToString(&response_reserialized));
  ASSERT_THAT(
      client_put_incoming_message(
          client_session, oak::session::BytesFromString(response_reserialized)),
      NoError());

  ASSERT_TRUE(server_is_open(server_session));
  ASSERT_TRUE(client_is_open(client_session));
}

TEST(OakSessionBindingsTest, TestHandshake) {
  ErrorOrServerSession server_session_result = new_server_session();
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result = new_client_session();
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, AcceptEmptyOutgoingMessage) {
  ErrorOrServerSession server_session_result = new_server_session();
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result = new_client_session();
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  ErrorOrBytes client_out = client_get_outgoing_message(client_session);
  ASSERT_THAT(client_out.error, Eq(nullptr));
  ASSERT_THAT(client_out.result, Eq(nullptr));

  ErrorOrBytes server_out = server_get_outgoing_message(server_session);
  ASSERT_THAT(server_out.error, Eq(nullptr));
  ASSERT_THAT(server_out.result, Eq(nullptr));

  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, AcceptEmptyRead) {
  ErrorOrServerSession server_session_result = new_server_session();
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result = new_client_session();
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  ErrorOrBytes client_out = client_read(client_session);
  ASSERT_THAT(client_out.error, Eq(nullptr));
  ASSERT_THAT(client_out.result, Eq(nullptr));

  ErrorOrBytes server_out = server_read(server_session);
  ASSERT_THAT(server_out.error, Eq(nullptr));
  ASSERT_THAT(server_out.result, Eq(nullptr));

  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, TestClientEncryptServerDecrypt) {
  ErrorOrServerSession server_session_result = new_server_session();
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result = new_client_session();
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  std::string msg = "Hello Client To Server";
  ASSERT_THAT(client_write(client_session, BytesFromString(msg)), NoError());

  ErrorOrBytes client_out = client_get_outgoing_message(client_session);
  ASSERT_THAT(client_out, IsResult());

  ASSERT_THAT(server_put_incoming_message(server_session, *client_out.result),
              NoError());
  free_bytes(client_out.result);

  ErrorOrBytes server_in = server_read(server_session);
  ASSERT_THAT(server_in, IsResult());

  ASSERT_EQ(msg, BytesToString(*server_in.result));
  free_bytes(server_in.result);

  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, TestServerEncryptClientDecrypt) {
  ErrorOrServerSession server_session_result = new_server_session();
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result = new_client_session();
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  std::string msg = "Hello Server to Client";
  ASSERT_THAT(server_write(server_session, BytesFromString(msg)), NoError());

  ErrorOrBytes server_out = server_get_outgoing_message(server_session);
  ASSERT_THAT(server_out, IsResult());

  ASSERT_THAT(client_put_incoming_message(client_session, *server_out.result),
              NoError());
  free_bytes(server_out.result);

  ErrorOrBytes client_in = client_read(client_session);
  ASSERT_THAT(client_in, IsResult());

  ASSERT_EQ(msg, BytesToString(*client_in.result));
  free_bytes(client_in.result);

  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, ErrorsAreReturned) {
  ErrorOrServerSession server_session_result = new_server_session();
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result = new_client_session();
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  ErrorOrBytes client_in = client_read(client_session);
  ASSERT_THAT(client_in, IsError());
  free_error(client_in.error);

  ErrorOrBytes server_in = server_read(server_session);
  ASSERT_THAT(server_in, IsError());
  free_error(server_in.error);

  free_server_session(server_session);
  free_client_session(client_session);
}

}  // namespace
}  // namespace oak::session
