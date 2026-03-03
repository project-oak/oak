/*
 * Copyright 2025 The Project Oak Authors
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
#include "oak_session/tls/oak_session_tls.h"

#include <queue>
#include <thread>

#include "absl/status/status_matchers.h"
#include "absl/status/statusor.h"
#include "absl/synchronization/mutex.h"
#include "gtest/gtest.h"
#include "oak_session/tls/util.h"
#include "openssl/base.h"
#include "openssl/ssl.h"

namespace oak::session::tls {
namespace {

using ::absl_testing::IsOk;
using ::absl_testing::StatusIs;
using ::testing::Eq;

constexpr char kTestServerKeyPath[] = "oak_session/tls/testing/test_server.key";
constexpr char kTestServerCertPath[] =
    "oak_session/tls/testing/test_server.pem";
constexpr char kTestClientKeyPath[] = "oak_session/tls/testing/test_client.key";
constexpr char kTestClientCertPath[] =
    "oak_session/tls/testing/test_client.pem";
constexpr char kTestCaCertPath[] = "oak_session/tls/testing/test_ca.pem";

// Forward declarations for test helpers (definitions at bottom of file).

// Performs the TLS handshake using the manual OakSessionTlsInitializer API
// until the client is ready. Used for testing the low-level handshake flow.
void HandshakeToClientReady(OakSessionTlsInitializer& server_initializer,
                            OakSessionTlsInitializer& client_initializer);

// Completes the server handshake by sending initial application data from
// the client. The server receives this data bundled with the final handshake.
void CompleteServerHandshakeWithData(
    OakSessionTlsInitializer& server_initializer, OakSessionTls& client_session,
    absl::string_view initial_data);

// Encrypts a message with the sender, decrypts with the receiver, and verifies
// the decrypted message matches the original.
void SendReceiveAndVerifyMessage(OakSessionTls& sender, OakSessionTls& receiver,
                                 absl::string_view message);

// Creates test data of the specified size with predictable content.
std::string CreateTestData(size_t size);

// Result of RunHandshake containing both client and server initialized
// sessions.
struct HandshakeResult {
  absl::StatusOr<InitializedSession> client;
  absl::StatusOr<InitializedSession> server;
};

// Runs NewInitializedSession for both client and server concurrently using
// thread-safe queues for communication. Returns both initialized sessions.
HandshakeResult RunHandshake(OakSessionTlsContext& client_ctx,
                             OakSessionTlsContext& server_ctx);

TEST(OakSessionTlsTest, ManualHandshake) {
  auto server_key = util::LoadPrivateKeyFromFile(kTestServerKeyPath);
  ASSERT_THAT(server_key, IsOk());
  auto server_cert = util::LoadCertificateFromFile(kTestServerCertPath);
  ASSERT_THAT(server_cert, IsOk());

  ServerContextConfig server_config{
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *server_key,
              .cert_asn1 = *server_cert,
          },
  };
  auto server_ctx = OakSessionTlsContext::Create(server_config);
  ASSERT_THAT(server_ctx, IsOk());

  ClientContextConfig client_config{
      .server_trust_anchor_path = std::string(kTestCaCertPath),
  };
  auto client_ctx = OakSessionTlsContext::Create(client_config);
  ASSERT_THAT(client_ctx, IsOk());

  // Manual handshake using OakSessionTlsInitializer
  auto server_initializer = (*server_ctx)->NewSession();
  ASSERT_THAT(server_initializer, IsOk());
  auto client_initializer = (*client_ctx)->NewSession();
  ASSERT_THAT(client_initializer, IsOk());

  HandshakeToClientReady(**server_initializer, **client_initializer);

  // The client should be ready to send data now.
  auto client_result = (*client_initializer)->GetOpenSession();
  ASSERT_THAT(client_result, IsOk());

  std::string client_message = "hello server";
  CompleteServerHandshakeWithData(**server_initializer, *client_result->session,
                                  client_message);

  auto server_result = (*server_initializer)->GetOpenSession();
  ASSERT_THAT(server_result, IsOk());
  // The initial application data is now in the InitializedSession struct.
  ASSERT_THAT(server_result->initial_data, Eq(client_message));

  // Send data from server to client.
  std::string server_message = "hello client";
  SendReceiveAndVerifyMessage(/*sender=*/*server_result->session,
                              /*receiver=*/*client_result->session,
                              server_message);

  // Send one more client message (non-initial)
  std::string client_message2 = "hello again client";
  SendReceiveAndVerifyMessage(/*sender=*/*client_result->session,
                              /*receiver=*/*server_result->session,
                              client_message2);
}

// Verify that PQC key exchange (X25519MLKEM768) is negotiated.
TEST(OakSessionTlsTest, PqcKeyExchangeNegotiated) {
  auto server_key = util::LoadPrivateKeyFromFile(kTestServerKeyPath);
  ASSERT_THAT(server_key, IsOk());
  auto server_cert = util::LoadCertificateFromFile(kTestServerCertPath);
  ASSERT_THAT(server_cert, IsOk());

  ServerContextConfig server_config{
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *server_key,
              .cert_asn1 = *server_cert,
          },
  };
  auto server_ctx = OakSessionTlsContext::Create(server_config);
  ASSERT_THAT(server_ctx, IsOk());

  ClientContextConfig client_config{
      .server_trust_anchor_path = std::string(kTestCaCertPath),
  };
  auto client_ctx = OakSessionTlsContext::Create(client_config);
  ASSERT_THAT(client_ctx, IsOk());

  auto result = RunHandshake(**client_ctx, **server_ctx);
  ASSERT_THAT(result.client, IsOk());
  ASSERT_THAT(result.server, IsOk());

  // Verify that X25519MLKEM768 (hybrid PQC) was negotiated.
  // SSL_GROUP_X25519_MLKEM768 = 0x11ec (4588)
  uint16_t client_group = result.client->session->GetNegotiatedGroup();
  uint16_t server_group = result.server->session->GetNegotiatedGroup();

  EXPECT_EQ(client_group, SSL_GROUP_X25519_MLKEM768)
      << "Expected PQC key exchange (X25519MLKEM768), got group ID: "
      << client_group;
  EXPECT_EQ(server_group, SSL_GROUP_X25519_MLKEM768)
      << "Expected PQC key exchange (X25519MLKEM768), got group ID: "
      << server_group;
}

constexpr char kTestUntrustedKeyPath[] =
    "oak_session/tls/testing/test_untrusted.key";
constexpr char kTestUntrustedCertPath[] =
    "oak_session/tls/testing/test_untrusted.pem";

// Verify that a server certificate not signed by the trusted CA is rejected.
TEST(OakSessionTlsTest, UntrustedCertificateRejected) {
  // Server uses a self-signed certificate NOT in the client's trust anchor.
  auto untrusted_key = util::LoadPrivateKeyFromFile(kTestUntrustedKeyPath);
  ASSERT_THAT(untrusted_key, IsOk());
  auto untrusted_cert = util::LoadCertificateFromFile(kTestUntrustedCertPath);
  ASSERT_THAT(untrusted_cert, IsOk());

  ServerContextConfig server_config{
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *untrusted_key,
              .cert_asn1 = *untrusted_cert,
          },
  };
  auto server_ctx = OakSessionTlsContext::Create(server_config);
  ASSERT_THAT(server_ctx, IsOk());

  // Client trusts only the test CA, not the untrusted self-signed cert.
  ClientContextConfig client_config{
      .server_trust_anchor_path = std::string(kTestCaCertPath),
  };
  auto client_ctx = OakSessionTlsContext::Create(client_config);
  ASSERT_THAT(client_ctx, IsOk());

  auto server_initializer = (*server_ctx)->NewSession();
  ASSERT_THAT(server_initializer, IsOk());
  auto client_initializer = (*client_ctx)->NewSession();
  ASSERT_THAT(client_initializer, IsOk());

  // Client sends ClientHello
  auto client_hello = (*client_initializer)->GetTLSFrame();
  ASSERT_THAT(client_hello, IsOk());

  // Server processes ClientHello
  ASSERT_THAT((*server_initializer)->PutTLSFrame(*client_hello), IsOk());

  // Server sends ServerHello + Certificate (untrusted)
  auto server_hello = (*server_initializer)->GetTLSFrame();
  ASSERT_THAT(server_hello, IsOk());

  // Client should reject the untrusted certificate
  auto result = (*client_initializer)->PutTLSFrame(*server_hello);
  EXPECT_THAT(result, StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(OakSessionTlsTest, CreateAndUseMtlsSession) {
  auto server_key = util::LoadPrivateKeyFromFile(kTestServerKeyPath);
  ASSERT_THAT(server_key, IsOk());
  auto server_cert = util::LoadCertificateFromFile(kTestServerCertPath);
  ASSERT_THAT(server_cert, IsOk());
  auto client_key = util::LoadPrivateKeyFromFile(kTestClientKeyPath);
  ASSERT_THAT(client_key, IsOk());
  auto client_cert = util::LoadCertificateFromFile(kTestClientCertPath);
  ASSERT_THAT(client_cert, IsOk());

  ServerContextConfig server_config{
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *server_key,
              .cert_asn1 = *server_cert,
          },
      .client_trust_anchor_path = std::string(kTestCaCertPath),
  };
  auto server_ctx = OakSessionTlsContext::Create(server_config);
  ASSERT_THAT(server_ctx, IsOk());

  ClientContextConfig client_config{
      .server_trust_anchor_path = std::string(kTestCaCertPath),
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *client_key,
              .cert_asn1 = *client_cert,
          },
  };
  auto client_ctx = OakSessionTlsContext::Create(client_config);
  ASSERT_THAT(client_ctx, IsOk());

  auto result = RunHandshake(**client_ctx, **server_ctx);
  ASSERT_THAT(result.client, IsOk());
  ASSERT_THAT(result.server, IsOk());

  // Verify sessions work by sending messages.
  SendReceiveAndVerifyMessage(*result.client->session, *result.server->session,
                              "hello from client");
  SendReceiveAndVerifyMessage(*result.server->session, *result.client->session,
                              "hello from server");
}

TEST(OakSessionTlsTest, ClientSetsTlsIdentServerDoesntRequest) {
  auto server_key = util::LoadPrivateKeyFromFile(kTestServerKeyPath);
  ASSERT_THAT(server_key, IsOk());
  auto server_cert = util::LoadCertificateFromFile(kTestServerCertPath);
  ASSERT_THAT(server_cert, IsOk());
  auto client_key = util::LoadPrivateKeyFromFile(kTestClientKeyPath);
  ASSERT_THAT(client_key, IsOk());
  auto client_cert = util::LoadCertificateFromFile(kTestClientCertPath);
  ASSERT_THAT(client_cert, IsOk());

  // Do not enable a trust anchor so the server does not request a client
  // certificate.
  ServerContextConfig server_config{
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *server_key,
              .cert_asn1 = *server_cert,
          },
  };
  auto server_ctx = OakSessionTlsContext::Create(server_config);
  ASSERT_THAT(server_ctx, IsOk());

  // Set client credentials (but server won't request them).
  ClientContextConfig client_config{
      .server_trust_anchor_path = std::string(kTestCaCertPath),
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *client_key,
              .cert_asn1 = *client_cert,
          },
  };
  auto client_ctx = OakSessionTlsContext::Create(client_config);
  ASSERT_THAT(client_ctx, IsOk());

  auto result = RunHandshake(**client_ctx, **server_ctx);
  ASSERT_THAT(result.client, IsOk());
  ASSERT_THAT(result.server, IsOk());
}

TEST(OakSessionTlsTest,
     ServerRequestsClientCertButClientDoesntSetFailsHandshake) {
  auto server_key = util::LoadPrivateKeyFromFile(kTestServerKeyPath);
  ASSERT_THAT(server_key, IsOk());
  auto server_cert = util::LoadCertificateFromFile(kTestServerCertPath);
  ASSERT_THAT(server_cert, IsOk());
  auto client_key = util::LoadPrivateKeyFromFile(kTestClientKeyPath);
  ASSERT_THAT(client_key, IsOk());
  auto client_cert = util::LoadCertificateFromFile(kTestClientCertPath);
  ASSERT_THAT(client_cert, IsOk());

  // Enable a client trust anchor, which will trigger client cert request.
  ServerContextConfig server_config{
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *server_key,
              .cert_asn1 = *server_cert,
          },
      .client_trust_anchor_path = std::string(kTestCaCertPath),
  };
  auto server_ctx = OakSessionTlsContext::Create(server_config);
  ASSERT_THAT(server_ctx, IsOk());

  // Don't set client credentials.
  ClientContextConfig client_config{
      .server_trust_anchor_path = std::string(kTestCaCertPath),

  };
  auto client_ctx = OakSessionTlsContext::Create(client_config);
  ASSERT_THAT(client_ctx, IsOk());

  // Handshake
  auto server_initializer = (*server_ctx)->NewSession();
  ASSERT_THAT(server_initializer, IsOk());
  auto client_initializer = (*client_ctx)->NewSession();
  ASSERT_THAT(client_initializer, IsOk());

  HandshakeToClientReady(**server_initializer, **client_initializer);

  // The client should be ready to send data now.
  auto client_result = (*client_initializer)->GetOpenSession();
  ASSERT_THAT(client_result, IsOk());

  // Now try to complete the handshake on the server side: it should fail.
  std::string client_message = "hello server";
  auto encrypted_initial_data = client_result->session->Encrypt(client_message);
  ASSERT_THAT(encrypted_initial_data, IsOk());

  ASSERT_THAT((*server_initializer)->PutTLSFrame(*encrypted_initial_data),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(OakSessionTlsTest, LargeDataTransfer) {
  auto server_key = util::LoadPrivateKeyFromFile(kTestServerKeyPath);
  ASSERT_THAT(server_key, IsOk());
  auto server_cert = util::LoadCertificateFromFile(kTestServerCertPath);
  ASSERT_THAT(server_cert, IsOk());

  ServerContextConfig server_config{
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *server_key,
              .cert_asn1 = *server_cert,
          },
  };
  auto server_ctx = OakSessionTlsContext::Create(server_config);
  ASSERT_THAT(server_ctx, IsOk());

  ClientContextConfig client_config{
      .server_trust_anchor_path = std::string(kTestCaCertPath),
  };
  auto client_ctx = OakSessionTlsContext::Create(client_config);
  ASSERT_THAT(client_ctx, IsOk());

  auto result = RunHandshake(**client_ctx, **server_ctx);
  ASSERT_THAT(result.client, IsOk());
  ASSERT_THAT(result.server, IsOk());

  // Test large data transfer (100 KB, larger than 16384 frame size)
  std::string large_message = CreateTestData(100000);
  SendReceiveAndVerifyMessage(*result.client->session, *result.server->session,
                              large_message);
  SendReceiveAndVerifyMessage(*result.server->session, *result.client->session,
                              large_message);
}

std::string CreateTestData(size_t size) {
  std::string data;
  data.resize(size);
  for (size_t i = 0; i < size; ++i) {
    data[i] = static_cast<char>(i % 256);
  }
  return data;
}

void HandshakeToClientReady(OakSessionTlsInitializer& server_initializer,
                            OakSessionTlsInitializer& client_initializer) {
  auto client_frame_1 = client_initializer.GetTLSFrame();
  ASSERT_THAT(client_frame_1, IsOk());
  ASSERT_THAT(server_initializer.PutTLSFrame(*client_frame_1), IsOk());

  auto server_frame_1 = server_initializer.GetTLSFrame();
  ASSERT_THAT(server_frame_1, IsOk());
  ASSERT_THAT(client_initializer.PutTLSFrame(*server_frame_1), IsOk());

  ASSERT_TRUE(client_initializer.IsReady());
}

void CompleteServerHandshakeWithData(
    OakSessionTlsInitializer& server_initializer, OakSessionTls& client_session,
    absl::string_view initial_data) {
  auto encrypted_initial_data = client_session.Encrypt(initial_data);
  ASSERT_THAT(encrypted_initial_data, IsOk());

  ASSERT_THAT(server_initializer.PutTLSFrame(*encrypted_initial_data), IsOk());

  ASSERT_TRUE(server_initializer.IsReady());
}

void SendReceiveAndVerifyMessage(OakSessionTls& sender, OakSessionTls& receiver,
                                 absl::string_view message) {
  auto encrypted_message = sender.Encrypt(message);
  ASSERT_THAT(encrypted_message, IsOk());
  auto decrypted_message = receiver.Decrypt(*encrypted_message);
  ASSERT_THAT(decrypted_message, IsOk());
  ASSERT_THAT(*decrypted_message, Eq(message));
}

HandshakeResult RunHandshake(OakSessionTlsContext& client_ctx,
                             OakSessionTlsContext& server_ctx) {
  std::queue<std::string> client_to_server;
  std::queue<std::string> server_to_client;
  absl::Mutex mtx;

  absl::StatusOr<InitializedSession> server_result;
  std::thread server_thread([&]() {
    server_result = server_ctx.NewInitializedSession(
        /*send=*/
        [&](absl::string_view data) {
          absl::MutexLock lock(&mtx);
          server_to_client.push(std::string(data));
          return absl::OkStatus();
        },
        /*receive=*/
        [&]() -> absl::StatusOr<std::string> {
          absl::MutexLock lock(&mtx);
          mtx.Await(absl::Condition(
              +[](std::queue<std::string>* q) { return !q->empty(); },
              &client_to_server));
          auto msg = client_to_server.front();
          client_to_server.pop();
          return msg;
        });
  });

  auto client_result = client_ctx.NewInitializedSession(
      /*send=*/
      [&](absl::string_view data) {
        absl::MutexLock lock(&mtx);
        client_to_server.push(std::string(data));
        return absl::OkStatus();
      },
      /*receive=*/
      [&]() -> absl::StatusOr<std::string> {
        absl::MutexLock lock(&mtx);
        mtx.Await(absl::Condition(
            +[](std::queue<std::string>* q) { return !q->empty(); },
            &server_to_client));
        auto msg = server_to_client.front();
        server_to_client.pop();
        return msg;
      });

  server_thread.join();

  return {std::move(client_result), std::move(server_result)};
}

}  // namespace
}  // namespace oak::session::tls
