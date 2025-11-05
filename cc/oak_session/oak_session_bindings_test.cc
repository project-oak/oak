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

#include "absl/log/log.h"
#include "cc/ffi/bytes_bindings.h"
#include "cc/ffi/bytes_view.h"
#include "cc/ffi/error_bindings.h"
#include "cc/oak_session/testing/matchers.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "proto/session/session.pb.h"

namespace oak::session::bindings {
namespace {

using ::oak::ffi::bindings::BytesView;
using ::oak::ffi::bindings::ErrorOrRustBytes;
using ::oak::ffi::bindings::free_error;
using ::oak::ffi::bindings::free_rust_bytes;
using ::oak::ffi::bindings::free_rust_bytes_contents;
using ::oak::session::v1::SessionRequest;
using ::oak::session::v1::SessionResponse;
using ::testing::ContainsRegex;
using ::testing::Eq;
using ::testing::Ne;

constexpr absl::string_view kClientKeyBytes =
    "clientkeybytes12clientkeybytes34";
constexpr absl::string_view kServerKeyBytes =
    "serverkeybytes12serverkeybytes34";

void DoHandshake(ServerSession* server_session, ClientSession* client_session) {
  while (!client_is_open(client_session) && !server_is_open(server_session)) {
    if (!client_is_open(client_session)) {
      ErrorOrRustBytes init = client_get_outgoing_message(client_session);
      ASSERT_THAT(init, IsResult());

      // We could just past init.result directly, but let's ensure that the
      // request successfully goes through the ser/deser properly.
      SessionRequest request;
      ASSERT_TRUE(request.ParseFromString(*init.result));
      std::string request_reserialized;
      ASSERT_TRUE(request.SerializeToString(&request_reserialized));
      BytesView request_bytes = BytesView(request_reserialized);
      free_rust_bytes(init.result);

      ASSERT_THAT(server_put_incoming_message(server_session, request_bytes),
                  NoError());
    }

    if (!server_is_open(server_session)) {
      ErrorOrRustBytes init_resp = server_get_outgoing_message(server_session);
      ASSERT_THAT(init_resp.error, NoError());

      if (init_resp.result != nullptr) {
        SessionResponse response;
        ASSERT_TRUE(response.ParseFromString(*init_resp.result));
        free_rust_bytes(init_resp.result);
        std::string response_reserialized;
        ASSERT_TRUE(response.SerializeToString(&response_reserialized));
        ASSERT_THAT(client_put_incoming_message(
                        client_session, BytesView(response_reserialized)),
                    NoError());
      }
    }
  }

  ASSERT_TRUE(server_is_open(server_session));
  ASSERT_TRUE(client_is_open(client_session));
}

SessionConfig* TestConfigUnattestedNN() {
  auto result = new_session_config_builder(ATTESTATION_TYPE_UNATTESTED,
                                           HANDSHAKE_TYPE_NOISE_NN);
  if (result.error != nullptr) {
    LOG(FATAL) << "Failed to create session config builder"
               << static_cast<absl::string_view>(result.error->message);
  }

  return session_config_builder_build(result.result);
}

SessionConfig* TestConfigAttestedNNServer() {
  auto result = new_session_config_builder(ATTESTATION_TYPE_SELF_UNIDIRECTIONAL,
                                           HANDSHAKE_TYPE_NOISE_NN);

  if (result.error != nullptr) {
    LOG(FATAL) << "Failed to create session config builder"
               << static_cast<absl::string_view>(result.error->message);
  }
  auto session_config_builder = result.result;

  std::string attester_id = "fake_attester";
  std::string fake_event = "fake event";
  std::string fake_platform = "fake platform";
  auto signing_key = new_random_signing_key();
  auto verifying_bytes = signing_key_verifying_key_bytes(signing_key);
  auto fake_evidence =
      new_fake_evidence(BytesView(verifying_bytes), BytesView(fake_event));
  free_rust_bytes_contents(verifying_bytes);
  auto attester = new_simple_attester(BytesView(fake_evidence));
  free_rust_bytes_contents(fake_evidence);
  if (attester.error != nullptr) {
    LOG(FATAL) << "Failed to create simple attester"
               << static_cast<absl::string_view>(attester.error->message);
  }
  session_config_builder = session_config_builder_add_self_attester(
      session_config_builder, BytesView(attester_id), attester.result);
  auto fake_endorsements = new_fake_endorsements(BytesView(fake_platform));
  auto endorser_result = new_simple_endorser(BytesView(fake_endorsements));
  free_rust_bytes_contents(fake_endorsements);
  if (endorser_result.error != nullptr) {
    LOG(FATAL) << "Failed to create simple endorser"
               << static_cast<absl::string_view>(
                      endorser_result.error->message);
  }
  session_config_builder = session_config_builder_add_self_endorser(
      session_config_builder, BytesView(attester_id), endorser_result.result);
  session_config_builder = session_config_builder_add_session_binder(
      session_config_builder, BytesView(attester_id), signing_key);
  free_signing_key(signing_key);
  return session_config_builder_build(session_config_builder);
}

SessionConfig* TestConfigAttestedNNClient() {
  auto result = new_session_config_builder(ATTESTATION_TYPE_PEER_UNIDIRECTIONAL,
                                           HANDSHAKE_TYPE_NOISE_NN);
  if (result.error != nullptr) {
    LOG(FATAL) << "Failed to create session config builder"
               << static_cast<absl::string_view>(result.error->message);
  }
  auto session_config_builder = result.result;

  std::string attester_id = "fake_attester";
  std::string fake_event = "fake event";
  std::string fake_platform = "fake platform";
  auto verifier = new_fake_attestation_verifier(BytesView(fake_event),
                                                BytesView(fake_platform));

  session_config_builder = session_config_builder_add_peer_verifier(
      session_config_builder, BytesView(attester_id), verifier);

  return session_config_builder_build(session_config_builder);
}

SessionConfig* TestConfigUnattestedNKClient(BytesView public_key) {
  auto result = new_session_config_builder(ATTESTATION_TYPE_UNATTESTED,
                                           HANDSHAKE_TYPE_NOISE_NK);
  if (result.error != nullptr) {
    LOG(FATAL) << "Failed to create session config builder"
               << static_cast<absl::string_view>(result.error->message);
  }
  auto session_config_builder = result.result;

  session_config_builder = session_config_builder_set_peer_static_public_key(
      session_config_builder, public_key);

  return session_config_builder_build(session_config_builder);
}

SessionConfig* TestConfigUnattestedNKServer(IdentityKey* identity_key) {
  auto result = new_session_config_builder(ATTESTATION_TYPE_UNATTESTED,
                                           HANDSHAKE_TYPE_NOISE_NK);
  if (result.error != nullptr) {
    LOG(FATAL) << "Failed to create session config builder"
               << static_cast<absl::string_view>(result.error->message);
  }
  auto session_config_builder = result.result;

  session_config_builder = session_config_builder_set_self_static_private_key(
      session_config_builder, identity_key);

  return session_config_builder_build(session_config_builder);
}

SessionConfig* TestConfigUnattestedKK(BytesView peer_public_key,
                                      IdentityKey* self_identity_key) {
  auto result = new_session_config_builder(ATTESTATION_TYPE_UNATTESTED,
                                           HANDSHAKE_TYPE_NOISE_KK);
  if (result.error != nullptr) {
    LOG(FATAL) << "Failed to create session config builder"
               << static_cast<absl::string_view>(result.error->message);
  }
  auto session_config_builder = result.result;

  session_config_builder = session_config_builder_set_self_static_private_key(
      session_config_builder, self_identity_key);

  session_config_builder = session_config_builder_set_peer_static_public_key(
      session_config_builder, peer_public_key);

  return session_config_builder_build(session_config_builder);
}

TEST(OakSessionBindingsTest, TestNNHandshake) {
  ErrorOrServerSession server_session_result =
      new_server_session(TestConfigUnattestedNN());
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result =
      new_client_session(TestConfigUnattestedNN());
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, TestNNHandshakeProvidesSessionToken) {
  ErrorOrServerSession server_session_result =
      new_server_session(TestConfigUnattestedNN());
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result =
      new_client_session(TestConfigUnattestedNN());
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  ErrorOrRustBytes client_session_binding_token =
      client_get_session_binding_token(client_session, BytesView("info"));
  ASSERT_THAT(client_session_binding_token, IsResult());
  ErrorOrRustBytes server_session_binding_token =
      server_get_session_binding_token(server_session, BytesView("info"));
  ASSERT_THAT(server_session_binding_token, IsResult());
  EXPECT_THAT(absl::string_view(*client_session_binding_token.result),
              Eq(absl::string_view(*server_session_binding_token.result)));

  free_rust_bytes(client_session_binding_token.result);
  free_rust_bytes(server_session_binding_token.result);
  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest,
     TestNNHandshakeProvidesDifferentSessionTokenForDifferentInfo) {
  ErrorOrServerSession server_session_result =
      new_server_session(TestConfigUnattestedNN());
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result =
      new_client_session(TestConfigUnattestedNN());
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  ErrorOrRustBytes client_session_binding_token =
      client_get_session_binding_token(client_session, BytesView("info"));
  ASSERT_THAT(client_session_binding_token, IsResult());
  ErrorOrRustBytes server_session_binding_token =
      server_get_session_binding_token(server_session, BytesView("wrong info"));
  ASSERT_THAT(server_session_binding_token, IsResult());
  EXPECT_THAT(absl::string_view(*client_session_binding_token.result),
              Ne(absl::string_view(*server_session_binding_token.result)));

  free_rust_bytes(client_session_binding_token.result);
  free_rust_bytes(server_session_binding_token.result);
  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, TestNKHandshake) {
  ErrorOrIdentityKey identity_key =
      new_identity_key_from_bytes(BytesView(kServerKeyBytes));
  ASSERT_THAT(identity_key, IsResult());
  ErrorOrRustBytes public_key =
      identity_key_get_public_key(identity_key.result);
  ASSERT_THAT(public_key, IsResult());

  ErrorOrServerSession server_session_result =
      new_server_session(TestConfigUnattestedNKServer(identity_key.result));
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result = new_client_session(
      TestConfigUnattestedNKClient(BytesView(*(public_key.result))));
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  free_rust_bytes(public_key.result);
  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, TestKKHandshake) {
  ErrorOrIdentityKey client_identity_key =
      new_identity_key_from_bytes(BytesView(kClientKeyBytes));
  ASSERT_THAT(client_identity_key, IsResult());
  ErrorOrIdentityKey server_identity_key =
      new_identity_key_from_bytes(BytesView(kServerKeyBytes));
  ASSERT_THAT(server_identity_key, IsResult());
  ErrorOrRustBytes client_public_key =
      identity_key_get_public_key(client_identity_key.result);
  ASSERT_THAT(client_public_key, IsResult());
  ErrorOrRustBytes server_public_key =
      identity_key_get_public_key(server_identity_key.result);
  ASSERT_THAT(server_public_key, IsResult());

  ErrorOrServerSession server_session_result =
      new_server_session(TestConfigUnattestedKK(
          BytesView(*(client_public_key.result)), server_identity_key.result));
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result =
      new_client_session(TestConfigUnattestedKK(
          BytesView(*(server_public_key.result)), client_identity_key.result));
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  free_rust_bytes(client_public_key.result);
  free_rust_bytes(server_public_key.result);
  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, AcceptEmptyOutgoingMessage) {
  ErrorOrServerSession server_session_result =
      new_server_session(TestConfigUnattestedNN());
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result =
      new_client_session(TestConfigUnattestedNN());
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  ErrorOrRustBytes client_out = client_get_outgoing_message(client_session);
  ASSERT_THAT(client_out.error, Eq(nullptr));
  ASSERT_THAT(client_out.result, Eq(nullptr));

  ErrorOrRustBytes server_out = server_get_outgoing_message(server_session);
  ASSERT_THAT(server_out.error, Eq(nullptr));
  ASSERT_THAT(server_out.result, Eq(nullptr));

  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, AcceptEmptyRead) {
  ErrorOrServerSession server_session_result =
      new_server_session(TestConfigUnattestedNN());
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result =
      new_client_session(TestConfigUnattestedNN());
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  ErrorOrRustBytes client_out = client_read(client_session);
  ASSERT_THAT(client_out.error, Eq(nullptr));
  ASSERT_THAT(client_out.result, Eq(nullptr));

  ErrorOrRustBytes server_out = server_read(server_session);
  ASSERT_THAT(server_out.error, Eq(nullptr));
  ASSERT_THAT(server_out.result, Eq(nullptr));

  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, TestClientEncryptServerDecryptUnattested) {
  ErrorOrServerSession server_session_result =
      new_server_session(TestConfigUnattestedNN());
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result =
      new_client_session(TestConfigUnattestedNN());
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  v1::PlaintextMessage plaintext_message_out;
  plaintext_message_out.set_plaintext("Hello Client To Server");
  ASSERT_THAT(
      client_write(client_session,
                   BytesView(plaintext_message_out.SerializeAsString())),
      NoError());

  ErrorOrRustBytes client_out = client_get_outgoing_message(client_session);
  ASSERT_THAT(client_out, IsResult());

  ASSERT_THAT(server_put_incoming_message(server_session,
                                          BytesView(*client_out.result)),
              NoError());
  free_rust_bytes(client_out.result);

  ErrorOrRustBytes server_in = server_read(server_session);
  ASSERT_THAT(server_in, IsResult());

  v1::PlaintextMessage plaintext_message_in;
  ASSERT_TRUE(plaintext_message_in.ParseFromString(*server_in.result));
  EXPECT_THAT(plaintext_message_in.plaintext(),
              Eq(plaintext_message_out.plaintext()));
  free_rust_bytes(server_in.result);

  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, TestClientEncryptServerDecryptAttested) {
  ErrorOrServerSession server_session_result =
      new_server_session(TestConfigAttestedNNServer());
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result =
      new_client_session(TestConfigAttestedNNClient());
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  v1::PlaintextMessage plaintext_message_out;
  plaintext_message_out.set_plaintext("Hello Client To Server");
  ASSERT_THAT(
      client_write(client_session,
                   BytesView(plaintext_message_out.SerializeAsString())),
      NoError());

  ErrorOrRustBytes client_out = client_get_outgoing_message(client_session);
  ASSERT_THAT(client_out, IsResult());

  ASSERT_THAT(server_put_incoming_message(server_session,
                                          BytesView(*client_out.result)),
              NoError());
  free_rust_bytes(client_out.result);

  ErrorOrRustBytes server_in = server_read(server_session);
  ASSERT_THAT(server_in, IsResult());

  v1::PlaintextMessage plaintext_message_in;
  ASSERT_TRUE(plaintext_message_in.ParseFromString(*server_in.result));
  EXPECT_THAT(plaintext_message_in.plaintext(),
              Eq(plaintext_message_out.plaintext()));
  free_rust_bytes(server_in.result);

  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, TestServerEncryptClientDecryptUnattested) {
  ErrorOrServerSession server_session_result =
      new_server_session(TestConfigUnattestedNN());
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result =
      new_client_session(TestConfigUnattestedNN());
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  DoHandshake(server_session, client_session);

  v1::PlaintextMessage plaintext_message_out;
  plaintext_message_out.set_plaintext("Hello Server to Client");
  ASSERT_THAT(
      server_write(server_session,
                   BytesView(plaintext_message_out.SerializeAsString())),
      NoError());

  ErrorOrRustBytes server_out = server_get_outgoing_message(server_session);
  ASSERT_THAT(server_out, IsResult());

  ASSERT_THAT(client_put_incoming_message(client_session,
                                          BytesView(*server_out.result)),
              NoError());
  free_rust_bytes(server_out.result);

  ErrorOrRustBytes client_in = client_read(client_session);
  ASSERT_THAT(client_in, IsResult());

  v1::PlaintextMessage plaintext_message_in;
  ASSERT_TRUE(plaintext_message_in.ParseFromString(*client_in.result));
  ASSERT_EQ(plaintext_message_in.plaintext(),
            plaintext_message_out.plaintext());
  free_rust_bytes(client_in.result);

  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, ErrorsAreReturned) {
  ErrorOrServerSession server_session_result =
      new_server_session(TestConfigUnattestedNN());
  ASSERT_THAT(server_session_result, IsResult());
  ServerSession* server_session = server_session_result.result;
  ErrorOrClientSession client_session_result =
      new_client_session(TestConfigUnattestedNN());
  ASSERT_THAT(client_session_result, IsResult());
  ClientSession* client_session = client_session_result.result;

  ErrorOrRustBytes client_in = client_read(client_session);
  ASSERT_THAT(client_in, IsError());
  free_error(client_in.error);

  ErrorOrRustBytes server_in = server_read(server_session);
  ASSERT_THAT(server_in, IsError());
  free_error(server_in.error);

  free_server_session(server_session);
  free_client_session(client_session);
}

TEST(OakSessionBindingsTest, IncorrectKeyLenReturnsError) {}

TEST(OakSessionBindingsTest, AttestationIds) {
  // Just make sure they're UUIDs.
  ASSERT_THAT(absl::string_view(certificate_based_attestation_id()),
              ContainsRegex("^([A-Fa-f0-9]+-){4}[A-Fa-f0-9]+$"));
  ASSERT_THAT(absl::string_view(confidential_space_attestation_id()),
              ContainsRegex("^([A-Fa-f0-9]+-){4}[A-Fa-f0-9]+$"));
}

}  // namespace
}  // namespace oak::session::bindings
