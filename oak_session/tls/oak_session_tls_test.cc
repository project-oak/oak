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

#include "absl/status/status_matchers.h"
#include "absl/status/statusor.h"
#include "gtest/gtest.h"
#include "openssl/base.h"
#include "openssl/ssl.h"

namespace oak::session::tls {
namespace {

using ::absl_testing::IsOk;
using ::absl_testing::StatusIs;
using ::testing::Eq;

absl::StatusOr<std::string> LoadPrivateKeyFromFile(const char* key_path);
absl::StatusOr<std::string> LoadCertificateFromFile(const char* cert_path);

constexpr char kTestServerKeyPath[] = "oak_session/tls/testing/server.key";
constexpr char kTestServerCertPath[] = "oak_session/tls/testing/server.pem";
constexpr char kTestClientKeyPath[] = "oak_session/tls/testing/client.key";
constexpr char kTestClientCertPath[] = "oak_session/tls/testing/client.pem";

void HandshakeToClientReady(OakSessionTlsInitializer& server_initializer,
                            OakSessionTlsInitializer& client_initializer);
void CompleteServerHandshakeWithData(
    OakSessionTlsInitializer& server_initializer, OakSessionTls& client_session,
    absl::string_view initial_data);
void SendReceiveAndVerifyMessage(OakSessionTls& sender, OakSessionTls& receiver,
                                 absl::string_view message);
std::string CreateTestData(size_t size);

TEST(OakSessionTlsTest, CreateAndUseSession) {
  auto server_key = LoadPrivateKeyFromFile(kTestServerKeyPath);
  ASSERT_THAT(server_key, IsOk());
  auto server_cert = LoadCertificateFromFile(kTestServerCertPath);
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
      .server_trust_anchor_path = std::string(kTestServerCertPath),
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
  auto client_session = (*client_initializer)->GetOpenClientSession();
  ASSERT_THAT(client_session, IsOk());

  std::string client_message = "hello server";
  CompleteServerHandshakeWithData(**server_initializer, **client_session,
                                  client_message);

  auto server_session = (*server_initializer)->GetOpenClientSession();
  ASSERT_THAT(server_session, IsOk());
  // The intial application data is stored in the initializer.
  ASSERT_THAT((*server_initializer)->initial_data(), Eq(client_message));

  // Send data from server to client.
  std::string server_message = "hello client";
  SendReceiveAndVerifyMessage(/*sender=*/**server_session,
                              /*receiver=*/**client_session, server_message);

  // Send one more client message (non-initial)
  std::string client_message2 = "hello again client";
  SendReceiveAndVerifyMessage(/*sender=*/**client_session,
                              /*receiver=*/**server_session, client_message2);
}

TEST(OakSessionTlsTest, CreateAndUseMtlsSession) {
  auto server_key = LoadPrivateKeyFromFile(kTestServerKeyPath);
  ASSERT_THAT(server_key, IsOk());
  auto server_cert = LoadCertificateFromFile(kTestServerCertPath);
  ASSERT_THAT(server_cert, IsOk());
  auto client_key = LoadPrivateKeyFromFile(kTestClientKeyPath);
  ASSERT_THAT(client_key, IsOk());
  auto client_cert = LoadCertificateFromFile(kTestClientCertPath);
  ASSERT_THAT(client_cert, IsOk());

  ServerContextConfig server_config{
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *server_key,
              .cert_asn1 = *server_cert,
          },
      .client_trust_anchor_path = std::string(kTestClientCertPath),
  };
  auto server_ctx = OakSessionTlsContext::Create(server_config);
  ASSERT_THAT(server_ctx, IsOk());

  ClientContextConfig client_config{
      .server_trust_anchor_path = std::string(kTestServerCertPath),
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *client_key,
              .cert_asn1 = *client_cert,
          },
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
  auto client_session = (*client_initializer)->GetOpenClientSession();
  ASSERT_THAT(client_session, IsOk());

  std::string client_message = "hello server";
  CompleteServerHandshakeWithData(**server_initializer, **client_session,
                                  client_message);

  auto server_session = (*server_initializer)->GetOpenClientSession();
  ASSERT_THAT(server_session, IsOk());
  // The intial application data is stored in the initializer.
  ASSERT_THAT((*server_initializer)->initial_data(), Eq(client_message));

  // Send data from server to client.
  std::string server_message = "hello client";
  SendReceiveAndVerifyMessage(/*sender=*/**server_session,
                              /*receiver=*/**client_session, server_message);

  // Send one more client message (non-initial)
  std::string client_message2 = "hello again client";
  SendReceiveAndVerifyMessage(/*sender=*/**client_session,
                              /*receiver=*/**server_session, client_message2);
}

TEST(OakSessionTlsTest, ClientSetsTlsIdentServerDoesntRequest) {
  auto server_key = LoadPrivateKeyFromFile(kTestServerKeyPath);
  ASSERT_THAT(server_key, IsOk());
  auto server_cert = LoadCertificateFromFile(kTestServerCertPath);
  ASSERT_THAT(server_cert, IsOk());
  auto client_key = LoadPrivateKeyFromFile(kTestClientKeyPath);
  ASSERT_THAT(client_key, IsOk());
  auto client_cert = LoadCertificateFromFile(kTestClientCertPath);
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

  // Set client credentials.
  ClientContextConfig client_config{
      .server_trust_anchor_path = std::string(kTestServerCertPath),
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *client_key,
              .cert_asn1 = *client_cert,
          },
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
  auto client_session = (*client_initializer)->GetOpenClientSession();
  ASSERT_THAT(client_session, IsOk());

  std::string client_message = "hello server";
  CompleteServerHandshakeWithData(**server_initializer, **client_session,
                                  client_message);
}

TEST(OakSessionTlsTest,
     ServerRequestsClientCertButClientDoesntSetFailsHandshake) {
  auto server_key = LoadPrivateKeyFromFile(kTestServerKeyPath);
  ASSERT_THAT(server_key, IsOk());
  auto server_cert = LoadCertificateFromFile(kTestServerCertPath);
  ASSERT_THAT(server_cert, IsOk());
  auto client_key = LoadPrivateKeyFromFile(kTestClientKeyPath);
  ASSERT_THAT(client_key, IsOk());
  auto client_cert = LoadCertificateFromFile(kTestClientCertPath);
  ASSERT_THAT(client_cert, IsOk());

  // Enable a client trust anchor, which will trigger client cert request.
  ServerContextConfig server_config{
      .tls_identity =
          TlsIdentity{
              .key_asn1 = *server_key,
              .cert_asn1 = *server_cert,
          },
      .client_trust_anchor_path = std::string(kTestClientCertPath),
  };
  auto server_ctx = OakSessionTlsContext::Create(server_config);
  ASSERT_THAT(server_ctx, IsOk());

  // Don't set client credentials.
  ClientContextConfig client_config{
      .server_trust_anchor_path = std::string(kTestServerCertPath),

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
  auto client_session = (*client_initializer)->GetOpenClientSession();
  ASSERT_THAT(client_session, IsOk());

  // Now try to complete the handshake on the server side: it should fail.
  std::string client_message = "hello server";
  auto encrypted_initial_data = (*client_session)->Encrypt(client_message);
  ASSERT_THAT(encrypted_initial_data, IsOk());

  ASSERT_THAT((*server_initializer)->PutTLSFrame(*encrypted_initial_data),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(OakSessionTlsTest, LargeDataTransfer) {
  auto server_key = LoadPrivateKeyFromFile(kTestServerKeyPath);
  ASSERT_THAT(server_key, IsOk());
  auto server_cert = LoadCertificateFromFile(kTestServerCertPath);
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
      .server_trust_anchor_path = std::string(kTestServerCertPath),
  };
  auto client_ctx = OakSessionTlsContext::Create(client_config);
  ASSERT_THAT(client_ctx, IsOk());

  // Handshake
  // Create initializers for client and server and do the handshake.
  auto server_initializer = (*server_ctx)->NewSession();
  ASSERT_THAT(server_initializer, IsOk());
  auto client_initializer = (*client_ctx)->NewSession();
  ASSERT_THAT(client_initializer, IsOk());

  HandshakeToClientReady(**server_initializer, **client_initializer);

  auto client_session = (*client_initializer)->GetOpenClientSession();
  ASSERT_THAT(client_session, IsOk());

  std::string client_message =
      CreateTestData(100000);  // 100 KB,larger than 16384 frame size
  CompleteServerHandshakeWithData(**server_initializer, **client_session,
                                  client_message);

  auto server_session = (*server_initializer)->GetOpenClientSession();
  ASSERT_THAT(server_session, IsOk());
  // The intial application data is stored in the initializer.
  ASSERT_THAT((*server_initializer)->initial_data(), Eq(client_message));

  // Send data from server to client.
  std::string server_message =
      CreateTestData(100000);  // 100 KB,larger than 16384 frame size
  SendReceiveAndVerifyMessage(/*sender=*/**server_session,
                              /*receiver=*/**client_session, server_message);

  // Send one more client message (non-initial)
  std::string client_message2 = CreateTestData(100000);  // 100 KB
  SendReceiveAndVerifyMessage(/*sender=*/**client_session,
                              /*receiver=*/**server_session, client_message2);
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

absl::StatusOr<std::string> LoadPrivateKeyFromFile(const char* key_path) {
  FILE* file = fopen(key_path, "r");
  if (file == nullptr) {
    return absl::InternalError("Failed to open private key file");
  }
  bssl::UniquePtr<EVP_PKEY> pkey(
      PEM_read_PrivateKey(file, nullptr, nullptr, nullptr));
  fclose(file);
  if (pkey == nullptr) {
    return absl::InternalError("Failed to read private key from file");
  }

  int der_len = i2d_PrivateKey(pkey.get(), NULL);
  if (der_len < 0) {
    return absl::InternalError("Failed to get DER length from certificate");
  }

  std::string pkey_der;
  pkey_der.resize(der_len);
  unsigned char* p = reinterpret_cast<unsigned char*>(pkey_der.data());

  der_len = i2d_PrivateKey(pkey.get(), &p);
  if (der_len < 0) {
    return absl::InternalError("Failed to convert certificate to DER");
  }

  return pkey_der;
}

absl::StatusOr<std::string> LoadCertificateFromFile(const char* cert_path) {
  FILE* file = fopen(cert_path, "r");
  if (file == nullptr) {
    return absl::InternalError("Failed to open certificate file");
  }
  bssl::UniquePtr<X509> cert(PEM_read_X509(file, nullptr, nullptr, nullptr));
  fclose(file);
  if (cert == nullptr) {
    return absl::InternalError("Failed to read certificate from file");
  }

  int der_len = i2d_X509(cert.get(), nullptr);
  if (der_len < 0) {
    return absl::InternalError("Failed to get DER length from certificate");
  }

  std::string cert_der;
  cert_der.resize(der_len);
  unsigned char* p = reinterpret_cast<unsigned char*>(cert_der.data());

  der_len = i2d_X509(cert.get(), &p);
  if (der_len < 0) {
    return absl::InternalError("Failed to convert certificate to DER");
  }

  return cert_der;
}

}  // namespace
}  // namespace oak::session::tls
