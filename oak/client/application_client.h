/*
 * Copyright 2019 The Project Oak Authors
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

#ifndef OAK_CLIENT_APPLICATION_CLIENT_H_
#define OAK_CLIENT_APPLICATION_CLIENT_H_

#include "absl/status/status.h"
#include "glog/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/label_metadata.h"
#include "oak/client/signature_metadata.h"
#include "oak/common/label.h"
#include "oak/common/nonce_generator.h"
#include "oak/common/oak_sign.h"
#include "oak/common/utils.h"

namespace oak {

// A client connected to a previously created Oak Application.
//
// It allows invoking the Oak Application as specified by the Oak Application policies.
//
// TODO(#752): Verify remote attestations.
class ApplicationClient {
 public:
  // Returns a grpc Channel connecting to the specified address initialised with the following
  // composite channel credentials:
  // - Channel credentials, which should usually be TLS credentials
  // - Oak Label call credentials, possibly attaching a specific Oak Label to each call
  //
  // Note that composite channel credentials are really channel credentials, plus a generator object
  // that modifies metadata for each call, and in this case it happens to always attach the same
  // metadata to each outgoing call.
  //
  // See https://grpc.io/docs/guides/auth/.
  static std::shared_ptr<grpc::Channel> CreateChannel(
      std::string addr, std::shared_ptr<grpc::ChannelCredentials> channel_credentials,
      std::shared_ptr<grpc::CallCredentials> call_credentials) {
    auto composite_credentials =
        grpc::CompositeChannelCredentials(channel_credentials, call_credentials);

    return grpc::CreateChannel(addr, composite_credentials);
  }

  // Returns a gRPC Channel connecting to the specified address, initialised with a fixed Oak Label.
  static std::shared_ptr<grpc::Channel> CreateChannel(
      std::string addr, std::shared_ptr<grpc::ChannelCredentials> channel_credentials,
      oak::label::Label label) {
    auto call_credentials =
        grpc::MetadataCredentialsFromPlugin(absl::make_unique<LabelMetadata>(label));
    return CreateChannel(addr, channel_credentials, call_credentials);
  }

  // Returns a gRPC Channel connecting to the specified address, initialised with a fixed Oak Label
  // and the given signature.
  static std::shared_ptr<grpc::Channel> CreateChannel(
      std::string addr, std::shared_ptr<grpc::ChannelCredentials> channel_credentials,
      oak::label::Label label, oak::identity::SignedChallenge signed_challenge) {
    auto label_call_credentials =
        grpc::MetadataCredentialsFromPlugin(absl::make_unique<LabelMetadata>(label));
    auto sign_call_credentials =
        grpc::MetadataCredentialsFromPlugin(absl::make_unique<SignatureMetadata>(signed_challenge));
    auto call_credentials =
        grpc::CompositeCallCredentials(label_call_credentials, sign_call_credentials);
    return CreateChannel(addr, channel_credentials, call_credentials);
  }

  // Gets TLS channel credentials with default options.
  static std::shared_ptr<grpc::ChannelCredentials> GetTlsChannelCredentials() {
    return grpc::SslCredentials(grpc::SslCredentialsOptions());
  }

  // Gets TLS channel credentials with the specified PEM-encoded CA root certificate.
  static std::shared_ptr<grpc::ChannelCredentials> GetTlsChannelCredentials(
      std::string pem_root_certs) {
    return grpc::SslCredentials(grpc::SslCredentialsOptions{.pem_root_certs = pem_root_certs});
  }

  // Loads the CA PEM-encoded non-default CA root certificate.
  static std::string LoadRootCert(std::string root_cert_path) {
    if (root_cert_path.empty()) {
      return "";
    }
    return utils::read_file(root_cert_path);
  }

  // Loads the PEM-encoded public key.
  static std::string LoadPublicKey(std::string public_key_path) {
    std::string public_key = utils::read_file(public_key_path);

    // Parse key file.
    auto patterns = {"-----BEGIN PUBLIC KEY-----", "-----END PUBLIC KEY-----", "\r", "\n"};
    for (std::string pattern : patterns) {
      size_t substring = public_key.find(pattern);
      if (substring != std::string::npos) {
        public_key.erase(substring, pattern.length());
      }
    }

    // Decode Base64 key.
    std::string decoded_public_key;
    if (!absl::Base64Unescape(public_key, &decoded_public_key)) {
      LOG(FATAL) << "Could not decode public key: " << public_key;
    }
    return decoded_public_key;
  }

  // Generates an ed25519 key pair, and return the private key. The public key can be derived from
  // the private key.
  static std::string GenerateKeyPair() { return oak::generate_ed25519_key_pair(); }

  // Signs the sha256 hash of the message using the given private key. Returns a SignedChallenge
  // containing the signed hash and the public key corresponding to the input private key.
  static oak::identity::SignedChallenge Sign(std::string private_key, std::string input_string) {
    return oak::sign_ed25519(private_key, input_string);
  }

  // Loads the PEM-encoded private key, and returns the raw private key.
  static std::string LoadPrivateKey(const std::string& filename) {
    auto pem_map = oak::utils::read_pem(filename);
    oak::identity::SignedChallenge signature;

    if (pem_map.find(kPrivateKeyPemTag) == pem_map.end()) {
      LOG(FATAL) << "No private key in the pem file";
    }
    std::string private_key;
    if (!absl::Base64Unescape(pem_map[kPrivateKeyPemTag], &private_key)) {
      LOG(FATAL) << "Failed to decode base64 private key";
    }
    return private_key;
  }

  // Stores the given private key as a base64-encoded string in a PEM file in the given path.
  static void StorePrivateKey(const std::string& private_key, const std::string& filename) {
    oak::store_private_key(private_key, filename);
  }
};

// Convert a grpc::StatusCode into human-readable string.
std::string status_code_to_string(grpc::StatusCode code) {
  switch (code) {
    case grpc::StatusCode::OK:
      return "OK";
    case grpc::StatusCode::CANCELLED:
      return "Canceled";
    case grpc::StatusCode::UNKNOWN:
      return "Unknown";
    case grpc::StatusCode::INVALID_ARGUMENT:
      return "InvalidArgument";
    case grpc::StatusCode::DEADLINE_EXCEEDED:
      return "DeadlineExceeded";
    case grpc::StatusCode::NOT_FOUND:
      return "NotFound";
    case grpc::StatusCode::ALREADY_EXISTS:
      return "AlreadyExists";
    case grpc::StatusCode::PERMISSION_DENIED:
      return "PermissionDenied";
    case grpc::StatusCode::RESOURCE_EXHAUSTED:
      return "ResourceExhausted";
    case grpc::StatusCode::FAILED_PRECONDITION:
      return "FailedPrecondition";
    case grpc::StatusCode::ABORTED:
      return "Aborted";
    case grpc::StatusCode::OUT_OF_RANGE:
      return "OutOfRange";
    case grpc::StatusCode::UNIMPLEMENTED:
      return "Unimplemented";
    case grpc::StatusCode::INTERNAL:
      return "Internal";
    case grpc::StatusCode::UNAVAILABLE:
      return "Unavailable";
    case grpc::StatusCode::DATA_LOSS:
      return "DataLoss";
    case grpc::StatusCode::UNAUTHENTICATED:
      return "Unauthenticated";
    default:
      return absl::StrCat("Code(", code, ")");
  }
}

}  // namespace oak

#endif  // OAK_CLIENT_APPLICATION_CLIENT_H_
