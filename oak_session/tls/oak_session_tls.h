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

#ifndef OAK_TLS_SESSION_OAK_SESSION_TLS_INITIALIZER_H_
#define OAK_TLS_SESSION_OAK_SESSION_TLS_INITIALIZER_H_

#include <optional>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "openssl/base.h"

namespace oak::session::tls {

class OakSessionTls;
class OakSessionTlsInitializer;

enum class OakSessionTlsMode { kClient, kServer };

// The public/private key pair that this node will use.
// Both values should be non-empty.
struct TlsIdentity {
  // The private key that this node will use during handshake. If left blank, no
  // private key will be set for this node to send as verification.
  std::string key_asn1;

  // The cerificate containing the public key corresponding to the private key
  // in self_key_asn1.
  std::string cert_asn1;
};

// Parameters to configure OakSessionTlsContext for server behavior.
struct ServerContextConfig {
  // The key and certificate to use for this server.
  TlsIdentity tls_identity;

  // Optional trust anchor path for the client.
  // If set, client verification mode will be enabled, and client verification
  // will be required.
  std::optional<std::string> client_trust_anchor_path;
};

// Parameters to configure OakSessionTlsContext for client behavior.
struct ClientContextConfig {
  // The path to a trust anchor that can verify the server.
  std::string server_trust_anchor_path;

  // If provided, the client will support (but not require) mTLS mode, and the
  // server can request a certificate for verification.
  std::optional<TlsIdentity> tls_identity;
};

/**
 * Managed an SSL Context that will be used to create Oak TLS sessions.
 */
class OakSessionTlsContext {
 public:
  static absl::StatusOr<std::unique_ptr<OakSessionTlsContext>> Create(
      const ClientContextConfig& config);
  static absl::StatusOr<std::unique_ptr<OakSessionTlsContext>> Create(
      const ServerContextConfig& config);

  // Create a new OakSessionTlsInitializer for a new session using this
  // context's current configuration.
  absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> NewSession();

  // Create a new OakSessionTlsInitializer for a new session using an
  // already-configured ssl_ctx.
  OakSessionTlsContext(OakSessionTlsMode mode, bssl::UniquePtr<SSL_CTX> ssl_ctx)
      : mode_(mode), ssl_ctx_(std::move(ssl_ctx)) {}

 private:
  OakSessionTlsMode mode_;
  bssl::UniquePtr<SSL_CTX> ssl_ctx_;
};

/**
 * Manage the initialization state of an opening Oak Session (TLS).
 *
 * While the session is not ready, incoming TLS frames should be provided to the
 * `PutTLSFrame` method, and the `GetTLSFrame` method should be checked to see
 * if there are additional outgoing messages.
 *
 * After putting or getting a frame, check the `IsReady` method to see if the is
 * ready. If it's ready,
 */
class OakSessionTlsInitializer {
 public:
  static absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> CreateServer(
      SSL_CTX* ssl_ctx);

  static absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> CreateClient(
      SSL_CTX* ssl_ctx);

  // Returns true if the handshake is complete.
  //
  // After the handshake is complete, the `GetOpenClientSession` method can be
  // used to get the open session for encrypting and decrypting application
  bool IsReady();

  // If the handshake is complete, returns an open Oak TLS session that can be
  // used to encrypt and decrypt application data.
  //
  // Otherwise, returns an error.
  //
  // This method can only be called once. After calling this method the first
  // time, any subsequent calls will return an error.
  //
  // In some cases, the handshake completion may be accompanied by some initial
  // data. So be sure to check the contents of `initial_data()` after retrieving
  // the session, and before discarding the initializer.
  absl::StatusOr<std::unique_ptr<OakSessionTls>> GetOpenClientSession();

  // Put an incoming TLS frame into the initializer.
  absl::Status PutTLSFrame(absl::string_view tlsFrame);

  // Got the next outgoing TLS frame. If the session has already reached the
  // ready state, this method will return an error.
  absl::StatusOr<std::string> GetTLSFrame();

  // If a handshake was completed as part of a compound message that also
  // contained application data, this method will return the application data.
  absl::string_view initial_data() const { return initial_data_; }

 private:
  static absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> Create(
      SSL_CTX* ssl_ctx);
  OakSessionTlsInitializer(bssl::UniquePtr<SSL> ssl, BIO* bio_read,
                           BIO* bio_write)
      : ssl_(std::move(ssl)), bio_read_(bio_read), bio_write_(bio_write) {};
  bssl::UniquePtr<SSL> ssl_;
  BIO* bio_read_;
  BIO* bio_write_;
  std::string initial_data_;
};

// Represents an open Oak Session (TLS) that can be used to encrypt and decrypt.
//
// Can not be constructed directionly, instead, you can get an initialized
// instance of an open session by successfully completing a handshake using
// OakSessionTlsInitializer.
class OakSessionTls {
 public:
  // Encrypts the message and returns the TLS frame that can be
  // send over the outer communication channel.
  absl::StatusOr<std::string> Encrypt(absl::string_view plaintext_message);

  // Decrypts the TLS frame sent over the outer channel and
  // returns the application level plaintext message.
  absl::StatusOr<std::string> Decrypt(absl::string_view tls_frame);

 private:
  // Initializers construct sessions.
  friend class OakSessionTlsInitializer;

  OakSessionTls(bssl::UniquePtr<SSL> ssl, BIO* bio_read, BIO* bio_write)
      : ssl_(std::move(ssl)), bio_read_(bio_read), bio_write_(bio_write) {};
  bssl::UniquePtr<SSL> ssl_;
  BIO* bio_read_;
  BIO* bio_write_;
};

}  // namespace oak::session::tls
#endif  // OAK_TLS_SESSION_OAK_SESSION_TLS_INITIALIZER_H_
