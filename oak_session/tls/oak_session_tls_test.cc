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

using ::absl_testing::IsOk;
using ::testing::Eq;

constexpr char kTestServerKeyPath[] = "oak_session/tls/testing/server.key";
constexpr char kTestServerCertPath[] = "oak_session/tls/testing/server.pem";

absl::StatusOr<bssl::UniquePtr<SSL_CTX>> CreateServerContext(
    const char* server_key_path, const char* server_cert_path) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_server_method()));
  if (!ctx) {
    return absl::InternalError("Failed to create SSL_CTX");
  }

  if (SSL_CTX_use_PrivateKey_file(ctx.get(), server_key_path,
                                  SSL_FILETYPE_PEM) != 1) {
    return absl::InternalError("Failed to load private key");
  }

  if (SSL_CTX_use_certificate_file(ctx.get(), server_cert_path,
                                   SSL_FILETYPE_PEM) != 1) {
    return absl::InternalError("Failed to load certificate");
  }
  return ctx;
}

absl::StatusOr<bssl::UniquePtr<SSL_CTX>> CreateClientContext(
    const std::string& server_cert_path) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_client_method()));
  if (!ctx) {
    return absl::InternalError("Failed to create SSL_CTX");
  }

  if (SSL_CTX_load_verify_locations(ctx.get(), server_cert_path.c_str(),
                                    nullptr) != 1) {
    return absl::InternalError("Failed to load server certificate");
  }
  return ctx;
}

TEST(OakSessionTlsTest, CreateAndUseSession) {
  auto server_ctx =
      CreateServerContext(kTestServerKeyPath, kTestServerCertPath);
  ASSERT_THAT(server_ctx, IsOk());

  auto client_ctx = CreateClientContext(kTestServerCertPath);
  ASSERT_THAT(client_ctx, IsOk());

  // Handshake
  auto server_initializer =
      oak::session::tls::OakSessionTlsInitializer::CreateServer(
          server_ctx->get());
  ASSERT_THAT(server_initializer, IsOk());
  auto client_initializer =
      oak::session::tls::OakSessionTlsInitializer::CreateClient(
          client_ctx->get());
  ASSERT_THAT(client_initializer, IsOk());

  auto client_frame_1 = (*client_initializer)->GetTLSFrame();
  ASSERT_THAT(client_frame_1, IsOk());
  ASSERT_THAT((*server_initializer)->PutTLSFrame(*client_frame_1), IsOk());

  auto server_frame_1 = (*server_initializer)->GetTLSFrame();
  ASSERT_THAT(server_frame_1, IsOk());
  ASSERT_THAT((*client_initializer)->PutTLSFrame(*server_frame_1), IsOk());

  // The client should be ready to send data now.
  ASSERT_TRUE((*client_initializer)->IsReady());
  auto client_session = (*client_initializer)->GetOpenClientSession();
  ASSERT_THAT(client_session, IsOk());

  std::string client_message = "hello server";
  auto encrypted_client_message = (*client_session)->Encrypt(client_message);
  ASSERT_THAT(encrypted_client_message, IsOk());

  // The server handshake isn't done yet, but this data frame will complete it.
  ASSERT_THAT((*server_initializer)->PutTLSFrame(*encrypted_client_message),
              IsOk());

  ASSERT_TRUE((*server_initializer)->IsReady());
  auto server_session = (*server_initializer)->GetOpenClientSession();
  ASSERT_THAT(server_session, IsOk());
  // The intial application data is stored in the initializer.
  ASSERT_THAT((*server_initializer)->initial_data(), Eq(client_message));

  // Send data from server to client.
  std::string server_message = "hello client";
  auto encrypted_server_message = (*server_session)->Encrypt(server_message);
  ASSERT_THAT(encrypted_server_message, IsOk());
  auto decrypted_server_message =
      (*client_session)->Decrypt(*encrypted_server_message);
  ASSERT_THAT(decrypted_server_message, IsOk());
  ASSERT_THAT(*decrypted_server_message, Eq(server_message));
}
