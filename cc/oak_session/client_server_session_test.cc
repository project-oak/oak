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

#include <string>

#include "absl/log/log.h"
#include "absl/status/status_matchers.h"
#include "absl/strings/string_view.h"
#include "cc/ffi/bytes_view.h"
#include "cc/ffi/rust_bytes.h"
#include "cc/oak_session/client_session.h"
#include "cc/oak_session/server_session.h"
#include "cc/oak_session/testing/matchers.h"
#include "cc/testing/protocol-buffer-matchers.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "proto/session/session.pb.h"

namespace oak::session {
namespace {

using ::absl_testing::IsOk;
using ::absl_testing::IsOkAndHolds;
using ::oak::ffi::RustBytes;
using ::oak::session::v1::SessionRequest;
using ::oak::session::v1::SessionResponse;
using ::oak::testing::proto_matchers::EqualsProto;
using ::oak::testing::proto_matchers::proto::IgnoringFieldPaths;
using ::oak::testing::proto_matchers::proto::Partially;
using ::testing::AllOf;
using ::testing::ElementsAre;
using ::testing::Eq;
using ::testing::IsEmpty;
using ::testing::Ne;
using ::testing::Not;
using ::testing::Optional;
using ::testing::Pair;
using ::testing::Property;
using ::testing::Ref;
using ::testing::ResultOf;
using ::testing::SizeIs;
using ::testing::UnorderedElementsAre;

constexpr absl::string_view kFakeAttesterId = "fake_attester";
constexpr absl::string_view kFakeEvent = "fake event";
constexpr absl::string_view kFakePlatform = "fake platform";

constexpr absl::string_view kClientKeyBytes =
    "clientkeybytes12clientkeybytes34";
constexpr absl::string_view kServerKeyBytes =
    "serverkeybytes12serverkeybytes34";

SessionConfigHolder TestConfigUnattestedNN() {
  return SessionConfigBuilder(AttestationType::kUnattested,
                              HandshakeType::kNoiseNN)
      .BuildHolder();
}

SessionConfigHolder TestConfigAttestedNNServer() {
  auto signing_key = bindings::new_random_signing_key();
  auto verifying_bytes = bindings::signing_key_verifying_key_bytes(signing_key);

  auto fake_evidence =
      bindings::new_fake_evidence(ffi::bindings::BytesView(verifying_bytes),
                                  ffi::bindings::BytesView(kFakeEvent));
  ffi::bindings::free_rust_bytes_contents(verifying_bytes);
  auto attester =
      bindings::new_simple_attester(ffi::bindings::BytesView(fake_evidence));
  if (attester.error != nullptr) {
    LOG(FATAL) << "Failed to create attester:"
               << ffi::bindings::ErrorIntoStatus(attester.error);
  }
  ffi::bindings::free_rust_bytes_contents(fake_evidence);

  auto fake_endorsements =
      bindings::new_fake_endorsements(ffi::bindings::BytesView(kFakePlatform));
  auto endorser = bindings::new_simple_endorser(
      ffi::bindings::BytesView(fake_endorsements));
  if (endorser.error != nullptr) {
    LOG(FATAL) << "Failed to create attester:" << attester.error;
  }

  ffi::bindings::free_rust_bytes_contents(fake_endorsements);

  auto builder = SessionConfigBuilder(AttestationType::kSelfUnidirectional,
                                      HandshakeType::kNoiseNN)
                     .AddSelfAttester(kFakeAttesterId, attester.result)
                     .AddSelfEndorser(kFakeAttesterId, endorser.result)
                     .AddSessionBinder(kFakeAttesterId, signing_key);

  bindings::free_signing_key(signing_key);

  return builder.BuildHolder();
}

SessionConfigHolder TestConfigAttestedNNClient() {
  auto verifier = bindings::new_fake_attestation_verifier(
      ffi::bindings::BytesView(kFakeEvent),
      ffi::bindings::BytesView(kFakePlatform));

  return SessionConfigBuilder(AttestationType::kPeerUnidirectional,
                              HandshakeType::kNoiseNN)
      .AddPeerVerifier(kFakeAttesterId, verifier)
      .BuildHolder();
}

SessionConfigHolder TestConfigUnattestedNKClient(absl::string_view public_key) {
  return SessionConfigBuilder(AttestationType::kUnattested,
                              HandshakeType::kNoiseNK)
      .SetPeerStaticPublicKey(public_key)
      .BuildHolder();
}

SessionConfigHolder TestConfigUnattestedNKServer(
    bindings::IdentityKey* identity_key) {
  return SessionConfigBuilder(AttestationType::kUnattested,
                              HandshakeType::kNoiseNK)
      .SetSelfStaticPrivateKey(identity_key)
      .BuildHolder();
}

SessionConfigHolder TestConfigUnattestedKK(
    absl::string_view peer_public_key,
    bindings::IdentityKey* self_private_key) {
  return SessionConfigBuilder(AttestationType::kUnattested,
                              HandshakeType::kNoiseKK)
      .SetPeerStaticPublicKey(peer_public_key)
      .SetSelfStaticPrivateKey(self_private_key)
      .BuildHolder();
}

void DoHandshake(ClientSession& client_session, ServerSession& server_session) {
  while (!client_session.IsOpen() && !server_session.IsOpen()) {
    if (!client_session.IsOpen()) {
      absl::StatusOr<std::optional<SessionRequest>> init =
          client_session.GetOutgoingMessage();
      ASSERT_THAT(init, IsOkAndHolds(Ne(std::nullopt)));
      ASSERT_THAT(server_session.PutIncomingMessage(**init), IsOk());
    }

    if (!server_session.IsOpen()) {
      absl::StatusOr<std::optional<SessionResponse>> init_resp =
          server_session.GetOutgoingMessage();
      ASSERT_THAT(init_resp, IsOk());
      if (*init_resp != std::nullopt) {
        ASSERT_THAT(client_session.PutIncomingMessage(**init_resp), IsOk());
      }
    }
  }

  EXPECT_THAT(client_session.IsOpen(), Eq(true));
  EXPECT_THAT(server_session.IsOpen(), Eq(true));
}

TEST(ClientServerSessionTest, MultipleUsageFails) {
  auto client_session_config = TestConfigUnattestedNN();
  EXPECT_THAT(ClientSession::Create(std::move(client_session_config)), IsOk());
  EXPECT_THAT(ClientSession::Create(std::move(client_session_config)),
              Not(IsOk()));
}

TEST(ClientServerSessionTest, UnattestedNNHandshakeSucceeds) {
  auto client_session = ClientSession::Create(TestConfigUnattestedNN());
  auto server_session = ServerSession::Create(TestConfigUnattestedNN());

  DoHandshake(**client_session, **server_session);
}

TEST(ClientServerSessionTest, UnattestedNNHandshakeProvidesSessionToken) {
  auto client_session = ClientSession::Create(TestConfigUnattestedNN());
  auto server_session = ServerSession::Create(TestConfigUnattestedNN());

  DoHandshake(**client_session, **server_session);

  absl::StatusOr<ffi::RustBytes> client_session_binding_token =
      (*client_session)->GetSessionBindingToken("info");
  ASSERT_THAT(client_session_binding_token, IsOk());

  absl::StatusOr<ffi::RustBytes> server_session_binding_token =
      (*server_session)->GetSessionBindingToken("info");
  ASSERT_THAT(server_session_binding_token, IsOk());

  EXPECT_THAT(*client_session_binding_token,
              Eq(absl::string_view(*server_session_binding_token)));

  EXPECT_THAT((*server_session)->GetPeerAttestationEvidence(),
              IsOkAndHolds(IgnoringFieldPaths({"handshake_hash"},
                                              EqualsProto(R"pb()pb"))));
  EXPECT_THAT(
      (*server_session)->GetPeerAttestationEvidence()->handshake_hash().size(),
      Eq(32));

  EXPECT_THAT((*client_session)->GetPeerAttestationEvidence(),
              IsOkAndHolds(IgnoringFieldPaths({"handshake_hash"},
                                              EqualsProto(R"pb()pb"))));
  EXPECT_THAT(
      (*server_session)->GetPeerAttestationEvidence()->handshake_hash().size(),
      Eq(32));
}

TEST(ClientServerSessionTest,
     UnattestedNNHandshakeProvidesDifferentSessionTokenForDifferentInfo) {
  auto client_session = ClientSession::Create(TestConfigUnattestedNN());
  auto server_session = ServerSession::Create(TestConfigUnattestedNN());

  DoHandshake(**client_session, **server_session);

  absl::StatusOr<ffi::RustBytes> client_session_binding_token =
      (*client_session)->GetSessionBindingToken("info");
  ASSERT_THAT(client_session_binding_token, IsOk());

  absl::StatusOr<ffi::RustBytes> server_session_binding_token =
      (*server_session)->GetSessionBindingToken("wrong info");
  ASSERT_THAT(server_session_binding_token, IsOk());

  EXPECT_THAT(*client_session_binding_token,
              Ne(absl::string_view(*server_session_binding_token)));
}

TEST(ClientServerSessionTest, AttestedNNHandshakeSucceeds) {
  auto client_session = ClientSession::Create(TestConfigAttestedNNClient());
  auto server_session = ServerSession::Create(TestConfigAttestedNNServer());

  DoHandshake(**client_session, **server_session);

  // The server sees no evidence from the client in this configuration, but the
  // handshake hash should be present.
  auto server_evidence = (*server_session)->GetPeerAttestationEvidence();
  ASSERT_THAT(server_evidence, IsOk());
  EXPECT_THAT(server_evidence->endorsed_evidence(), IsEmpty());
  EXPECT_THAT(server_evidence->session_bindings(), IsEmpty());
  EXPECT_THAT(server_evidence->handshake_hash().size(), Eq(32));

  // The client sees evidence from the server.
  auto client_evidence = (*client_session)->GetPeerAttestationEvidence();
  ASSERT_THAT(client_evidence, IsOk());
  EXPECT_THAT(
      client_evidence->endorsed_evidence(),
      UnorderedElementsAre(
          Pair("fake_attester", Partially(EqualsProto(R"pb(
                 evidence {
                   application_keys {}
                   event_log { encoded_events: "fake event" }
                 }
                 endorsements { platform { id: "fake" value: "fake platform" } }
               )pb")))));
  EXPECT_THAT(client_evidence->session_bindings(),
              UnorderedElementsAre(Pair(
                  "fake_attester",
                  Property(&v1::SessionBinding::binding, Not(IsEmpty())))));
  EXPECT_THAT(client_evidence->handshake_hash().size(), Eq(32));
}

TEST(ClientServerSessionTest, UnattestedNKHandshakeSucceeds) {
  bindings::ErrorOrIdentityKey identity_key =
      bindings::new_identity_key_from_bytes(
          ffi::bindings::BytesView(kServerKeyBytes));
  ASSERT_THAT(identity_key, IsResult());
  ffi::bindings::ErrorOrRustBytes public_key =
      bindings::identity_key_get_public_key(identity_key.result);
  ASSERT_THAT(public_key, IsResult());

  auto client_session =
      ClientSession::Create(TestConfigUnattestedNKClient(*public_key.result));
  auto server_session =
      ServerSession::Create(TestConfigUnattestedNKServer(identity_key.result));

  DoHandshake(**client_session, **server_session);

  ffi::bindings::free_rust_bytes(public_key.result);
}

TEST(ClientServerSessionTest, UnattestedKKHandshakeSucceeds) {
  bindings::ErrorOrIdentityKey client_identity_key =
      bindings::new_identity_key_from_bytes(
          ffi::bindings::BytesView(kClientKeyBytes));
  ASSERT_THAT(client_identity_key, IsResult());
  ffi::bindings::ErrorOrRustBytes client_public_key =
      bindings::identity_key_get_public_key(client_identity_key.result);
  ASSERT_THAT(client_public_key, IsResult());

  bindings::ErrorOrIdentityKey server_identity_key =
      bindings::new_identity_key_from_bytes(
          ffi::bindings::BytesView(kServerKeyBytes));
  ASSERT_THAT(server_identity_key, IsResult());
  ffi::bindings::ErrorOrRustBytes server_public_key =
      bindings::identity_key_get_public_key(server_identity_key.result);
  ASSERT_THAT(client_public_key, IsResult());

  auto client_session = ClientSession::Create(TestConfigUnattestedKK(
      *server_public_key.result, client_identity_key.result));
  auto server_session = ServerSession::Create(TestConfigUnattestedKK(
      *client_public_key.result, server_identity_key.result));

  DoHandshake(**client_session, **server_session);

  ffi::bindings::free_rust_bytes(client_public_key.result);
  ffi::bindings::free_rust_bytes(server_public_key.result);
}

TEST(ClientServerSessionTest, AcceptEmptyOutgoingMessageResult) {
  auto client_session = ClientSession::Create(TestConfigUnattestedNN());
  auto server_session = ServerSession::Create(TestConfigUnattestedNN());

  DoHandshake(**client_session, **server_session);

  absl::StatusOr<std::optional<SessionRequest>> request =
      (*client_session)->GetOutgoingMessage();
  ASSERT_THAT(request, IsOkAndHolds(Eq(std::nullopt)));

  absl::StatusOr<std::optional<SessionResponse>> response =
      (*server_session)->GetOutgoingMessage();
  ASSERT_THAT(response, IsOkAndHolds(Eq(std::nullopt)));
}

TEST(ClientServerSessionTest, AcceptEmptyReadResult) {
  auto client_session = ClientSession::Create(TestConfigUnattestedNN());
  auto server_session = ServerSession::Create(TestConfigUnattestedNN());

  DoHandshake(**client_session, **server_session);

  absl::StatusOr<std::optional<v1::PlaintextMessage>> client_read =
      (*client_session)->Read();
  ASSERT_THAT(client_read, IsOkAndHolds(Eq(std::nullopt)));

  absl::StatusOr<std::optional<v1::PlaintextMessage>> server_read =
      (*server_session)->Read();
  ASSERT_THAT(server_read, IsOkAndHolds(Eq(std::nullopt)));
}

TEST(ClientServerSessionTest, ClientEncryptServerDecrypt) {
  auto client_session = ClientSession::Create(TestConfigUnattestedNN());
  auto server_session = ServerSession::Create(TestConfigUnattestedNN());

  DoHandshake(**client_session, **server_session);

  std::string plaintext_message = "Hello Server";
  v1::PlaintextMessage plaintext_message_request;
  plaintext_message_request.set_plaintext(plaintext_message);

  ASSERT_THAT((*client_session)->Write(plaintext_message_request), IsOk());

  absl::StatusOr<std::optional<SessionRequest>> request =
      (*client_session)->GetOutgoingMessage();
  ASSERT_THAT(request, IsOkAndHolds(Ne(std::nullopt)));

  ASSERT_THAT((*server_session)->PutIncomingMessage(**request), IsOk());
  absl::StatusOr<std::optional<v1::PlaintextMessage>> received_request =
      (*server_session)->Read();
  ASSERT_THAT(received_request, IsOkAndHolds(Ne(std::nullopt)));
  EXPECT_THAT(((*received_request)->plaintext()), Eq(plaintext_message));
}

TEST(ClientServerSessionTest, ClientEncryptServerDecryptRaw) {
  auto client_session = ClientSession::Create(TestConfigUnattestedNN());
  auto server_session = ServerSession::Create(TestConfigUnattestedNN());

  DoHandshake(**client_session, **server_session);

  std::string plaintext_message = "Hello Server";

  ASSERT_THAT((*client_session)->Write(plaintext_message), IsOk());
  absl::StatusOr<std::optional<SessionRequest>> request =
      (*client_session)->GetOutgoingMessage();
  ASSERT_THAT(request, IsOkAndHolds(Ne(std::nullopt)));

  ASSERT_THAT((*server_session)->PutIncomingMessage(**request), IsOk());
  absl::StatusOr<std::optional<RustBytes>> received_request =
      (*server_session)->ReadToRustBytes();
  ASSERT_THAT(received_request, IsOkAndHolds(Ne(std::nullopt)));

  EXPECT_THAT(**received_request, Eq(plaintext_message));
}

TEST(ClientServerSessionTest, ServerEncryptClientDecrypt) {
  auto client_session = ClientSession::Create(TestConfigUnattestedNN());
  auto server_session = ServerSession::Create(TestConfigUnattestedNN());

  DoHandshake(**client_session, **server_session);

  std::string response_message = "Hello Client";
  v1::PlaintextMessage plaintext_message_response;
  plaintext_message_response.set_plaintext(response_message);

  ASSERT_THAT((*server_session)->Write(plaintext_message_response), IsOk());
  absl::StatusOr<std::optional<SessionResponse>> response =
      (*server_session)->GetOutgoingMessage();
  ASSERT_THAT(response, IsOkAndHolds(Ne(std::nullopt)));

  ASSERT_THAT((*client_session)->PutIncomingMessage(**response), IsOk());
  absl::StatusOr<std::optional<v1::PlaintextMessage>> received_request =
      (*client_session)->Read();
  ASSERT_THAT(received_request, IsOkAndHolds(Ne(std::nullopt)));

  EXPECT_THAT(((*received_request)->plaintext()), Eq(response_message));
}

TEST(ClientServerSessionTest, ServerEncryptClientDecryptRaw) {
  auto client_session = ClientSession::Create(TestConfigUnattestedNN());
  auto server_session = ServerSession::Create(TestConfigUnattestedNN());

  DoHandshake(**client_session, **server_session);

  std::string response_message = "Hello Client";

  ASSERT_THAT((*server_session)->Write(response_message), IsOk());
  absl::StatusOr<std::optional<SessionResponse>> response =
      (*server_session)->GetOutgoingMessage();
  ASSERT_THAT(response, IsOkAndHolds(Ne(std::nullopt)));

  ASSERT_THAT((*client_session)->PutIncomingMessage(**response), IsOk());
  absl::StatusOr<std::optional<RustBytes>> received_request =
      (*client_session)->ReadToRustBytes();

  ASSERT_THAT(received_request, IsOkAndHolds(Optional(Eq(response_message))));
}

TEST(ClientServerSessionTest, ConvertsToStringView) {
  auto client_session = ClientSession::Create(TestConfigUnattestedNN());
  auto server_session = ServerSession::Create(TestConfigUnattestedNN());

  DoHandshake(**client_session, **server_session);

  std::string plaintext_message = "Hello Server";

  ASSERT_THAT((*client_session)->Write(plaintext_message), IsOk());
  absl::StatusOr<std::optional<SessionRequest>> request =
      (*client_session)->GetOutgoingMessage();
  ASSERT_THAT(request, IsOkAndHolds(Ne(std::nullopt)));

  ASSERT_THAT((*server_session)->PutIncomingMessage(**request), IsOk());
  absl::StatusOr<std::optional<RustBytes>> received_request =
      (*server_session)->ReadToRustBytes();
  ASSERT_THAT(received_request, IsOkAndHolds(Ne(std::nullopt)));

  absl::string_view received_request_string_view(**received_request);
  EXPECT_THAT(received_request_string_view, Eq(plaintext_message));
}

TEST(ClientServerSessionTest, ConvertsToString) {
  auto client_session = ClientSession::Create(TestConfigUnattestedNN());
  auto server_session = ServerSession::Create(TestConfigUnattestedNN());

  DoHandshake(**client_session, **server_session);

  std::string plaintext_message = "Hello Server";

  ASSERT_THAT((*client_session)->Write(plaintext_message), IsOk());
  absl::StatusOr<std::optional<SessionRequest>> request =
      (*client_session)->GetOutgoingMessage();
  ASSERT_THAT(request, IsOkAndHolds(Ne(std::nullopt)));

  // Let Rust Bytes go out of scope before doing comparison to verify copy
  // behavior.
  std::string received_request_string;
  [&]() {
    ASSERT_THAT((*server_session)->PutIncomingMessage(**request), IsOk());
    absl::StatusOr<std::optional<RustBytes>> received_request =
        (*server_session)->ReadToRustBytes();
    ASSERT_THAT(received_request,
                IsOkAndHolds(Optional(Eq(plaintext_message))));
    received_request_string = std::string(**received_request);
  }();

  EXPECT_THAT(received_request_string, Eq(plaintext_message));
}

}  // namespace
}  // namespace oak::session
