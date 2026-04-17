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

#include <functional>
#include <optional>

#include "absl/functional/any_invocable.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "openssl/base.h"
#include "openssl/ssl.h"

namespace oak::session::tls {

class OakSessionTls;
class OakSessionTlsInitializer;

enum class OakSessionTlsMode { kClient, kServer };

// Function type for sending data over the wire.
// The callback should block until the data is sent.
using SendFn = std::function<absl::Status(absl::string_view data)>;

// Function type for receiving data from the wire.
// The callback should block until data is available.
using ReceiveFn = std::function<absl::StatusOr<std::string>()>;

// Result of a successful handshake via NewInitializedSession.
struct InitializedSession {
  // The initialized session, ready for encrypt/decrypt operations.
  std::unique_ptr<OakSessionTls> session;

  // Application data received bundled with the final handshake message.
  // This is typically only populated on the server side.
  std::string initial_data;
};

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

// A custom certificate verifier callback.
// Takes the full DER-encoded certificate chain as input.
// Normal validation is performed first; if it succeeds, this callback is
// invoked.
using CustomCertVerifier =
    std::function<absl::Status(const std::vector<std::string>& cert_chain)>;

// Provider interface that returns a TlsIdentity.
// Called each time a new session is created on the context.
class TlsIdentityProvider {
 public:
  virtual ~TlsIdentityProvider() = default;
  virtual absl::StatusOr<TlsIdentity> GetIdentity() = 0;
};

// Parameters to configure OakSessionTlsContext for server behavior.
struct ServerContextConfig {
  // Provider that returns the key and certificate for this server.
  // Called each time a new session is created.
  std::unique_ptr<TlsIdentityProvider> tls_identity_provider;

  // Optional trust anchor path for the client.
  // If set, client verification mode will be enabled, and client verification
  // will be required.
  std::optional<std::string> client_trust_anchor_path;

  // Optional custom certificate verifier. If provided, standard verification
  // will occur first, followed by the custom verification logic.
  std::optional<CustomCertVerifier> custom_cert_verifier;
};

// Parameters to configure OakSessionTlsContext for client behavior.
struct ClientContextConfig {
  // The path to a trust anchor that can verify the server.
  std::string server_trust_anchor_path;

  // If provided, called each time a new session is created to get the
  // client's TLS identity. Enables mTLS mode, allowing the server to
  // request a certificate for verification.
  std::unique_ptr<TlsIdentityProvider> tls_identity_provider;

  // Optional custom certificate verifier. If provided, standard verification
  // will occur first, followed by the custom verification logic.
  std::optional<CustomCertVerifier> custom_cert_verifier;
};

/**
 * Manages an SSL Context that will be used to create Oak TLS sessions.
 *
 * For most use cases, use NewInitializedSession() which handles the TLS
 * handshake automatically. Use NewSession() only if you need fine-grained
 * control over the handshake process (e.g., for async I/O or custom framing).
 */
class OakSessionTlsContext {
 public:
  static absl::StatusOr<std::unique_ptr<OakSessionTlsContext>> Create(
      ClientContextConfig config);
  static absl::StatusOr<std::unique_ptr<OakSessionTlsContext>> Create(
      ServerContextConfig config);

  // Create a new session and perform the TLS handshake using the provided
  // send/receive callbacks. Returns an initialized session ready for use.
  //
  // This is the recommended API for most use cases. The callbacks should be
  // blocking: send() should block until the data is sent, and receive() should
  // block until data is available.
  //
  // Example:
  //   auto result = context->NewInitializedSession(
  //       [&](absl::string_view data) { return socket.Send(data); },
  //       [&]() { return socket.Receive(); });
  absl::StatusOr<InitializedSession> NewInitializedSession(SendFn send,
                                                           ReceiveFn receive);

  // Create a new OakSessionTlsInitializer for manual handshake control.
  //
  // Use this only if you need to drive the handshake yourself (e.g., for
  // async I/O or custom transport framing). For most use cases, prefer
  // NewInitializedSession() instead.
  //
  // When using this API, you must correctly implement the handshake loop:
  // - Client: send initial frame, then loop (receive, process, send response)
  // - Server: loop (receive, process, send response)
  // - After IsReady(), call GetOpenSession() to get the initialized session
  absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> NewSession();

  OakSessionTlsContext(
      OakSessionTlsMode mode, bssl::UniquePtr<SSL_CTX> ssl_ctx,
      std::unique_ptr<TlsIdentityProvider> tls_identity_provider,
      std::optional<CustomCertVerifier> custom_cert_verifier)
      : mode_(mode),
        ssl_ctx_(std::move(ssl_ctx)),
        tls_identity_provider_(std::move(tls_identity_provider)),
        custom_cert_verifier_(std::move(custom_cert_verifier)) {}

 private:
  OakSessionTlsMode mode_;
  bssl::UniquePtr<SSL_CTX> ssl_ctx_;
  std::unique_ptr<TlsIdentityProvider> tls_identity_provider_;
  std::optional<CustomCertVerifier> custom_cert_verifier_;
};

/**
 * Manages the initialization state of an opening Oak TLS session.
 *
 * This class is used for manual handshake control. For most use cases,
 * prefer OakSessionTlsContext::NewInitializedSession() instead.
 *
 * Handshake flow:
 * 1. For clients: call GetTLSFrame() to get the initial ClientHello and send it
 * 2. Loop until IsReady():
 *    a. Receive data from peer and pass to PutTLSFrame()
 *    b. If not ready, call GetTLSFrame() and send any response
 * 3. Call GetOpenSession() to get the initialized session
 */
class OakSessionTlsInitializer {
 public:
  static absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> CreateServer(
      SSL_CTX* ssl_ctx, const TlsIdentity* tls_identity = nullptr,
      const CustomCertVerifier* custom_cert_verifier = nullptr);

  static absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> CreateClient(
      SSL_CTX* ssl_ctx, const TlsIdentity* tls_identity = nullptr,
      const CustomCertVerifier* custom_cert_verifier = nullptr);

  // Returns true if the handshake is complete.
  //
  // After the handshake is complete, the `GetOpenSession` method can be
  // used to get the open session for encrypting and decrypting application
  bool IsReady();

  // If the handshake is complete, returns an initialized session containing
  // the open Oak TLS session and any initial application data received.
  //
  // Otherwise, returns an error.
  //
  // This method can only be called once. After calling this method the first
  // time, any subsequent calls will return an error.
  absl::StatusOr<InitializedSession> GetOpenSession();

  // Put an incoming TLS frame into the initializer for processing.
  absl::Status PutTLSFrame(absl::string_view tlsFrame);

  // Get the next outgoing TLS frame to send to the peer.
  // Returns an empty string if there is no pending outgoing data.
  absl::StatusOr<std::string> GetTLSFrame();

 private:
  static absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> Create(
      SSL_CTX* ssl_ctx, const TlsIdentity* tls_identity = nullptr,
      const CustomCertVerifier* custom_cert_verifier = nullptr);
  OakSessionTlsInitializer(bssl::UniquePtr<SSL> ssl, BIO* bio_read,
                           BIO* bio_write,
                           std::optional<CustomCertVerifier> custom_verifier)
      : ssl_(std::move(ssl)),
        bio_read_(bio_read),
        bio_write_(bio_write),
        custom_verifier_(std::move(custom_verifier)) {};
  bssl::UniquePtr<SSL> ssl_;
  BIO* bio_read_;
  BIO* bio_write_;
  std::string initial_data_;
  std::optional<CustomCertVerifier> custom_verifier_;
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

  // Returns the TLS group ID (key exchange algorithm) negotiated during
  // handshake. Returns 0 if no group was negotiated (e.g., for TLS < 1.3).
  // Common values:
  //   - SSL_GROUP_X25519_MLKEM768 (0x11ec / 4588): Hybrid PQC
  //   - SSL_GROUP_X25519 (29): Classical X25519
  uint16_t GetNegotiatedGroup() const;

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
