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

#include "cc/containers/sdk/standalone/oak_standalone.h"

#include <cstdint>

#include "absl/log/log.h"
#include "absl/status/status_matchers.h"
#include "cc/attestation/verification/attestation_verifier.h"
#include "cc/attestation/verification/insecure_attestation_verifier.h"
#include "cc/crypto/client_encryptor.h"
#include "cc/crypto/encryption_key.h"
#include "cc/crypto/hpke/recipient_context.h"
#include "cc/crypto/server_encryptor.h"
#include "gtest/gtest.h"
#include "proto/attestation/endorsement.pb.h"
#include "proto/attestation/evidence.pb.h"
#include "proto/attestation/verification.pb.h"
#include "proto/crypto/crypto.pb.h"

namespace oak::containers::sdk::standalone {

using ::absl_testing::IsOk;
using ::oak::attestation::v1::AttestationResults;
using ::oak::attestation::verification::InsecureAttestationVerifier;
using ::oak::crypto::ClientEncryptor;
using ::oak::crypto::DecryptionResult;
using ::oak::crypto::EncryptionKeyProvider;
using ::oak::crypto::KeyPair;
using ::oak::crypto::ServerEncryptor;
using ::oak::crypto::v1::EncryptedRequest;
using ::oak::crypto::v1::EncryptedResponse;
using ::oak::session::v1::EndorsedEvidence;
using ::testing::Eq;

namespace {
TEST(OakStandaloneTest, GetEndorsedEvidenceProvidesValidKeys) {
  // This test validates that we can:
  //   * Create a Keypair in C++
  //   * Send it to Rust to use the standalone evidence helper
  //   * Receive a valid endorsed evidence back from Rust.
  //   * The public keys in the evidence match the keypair we provided.

  // Set up our new Keypair and get an EndorsedEvidence from Rust.
  absl::StatusOr<KeyPair> key_pair = KeyPair::Generate();
  ASSERT_TRUE(key_pair.ok()) << key_pair.status();
  absl::StatusOr<EndorsedEvidence> endorsed_evidence =
      GetEndorsedEvidence(*key_pair);
  ASSERT_THAT(endorsed_evidence, IsOk());

  // Verify that the endorsed evidence is valid.
  InsecureAttestationVerifier verifier;
  absl::StatusOr<AttestationResults> attestation_results = verifier.Verify(
      std::chrono::system_clock::now(), endorsed_evidence->evidence(),
      endorsed_evidence->endorsements());
  ASSERT_THAT(attestation_results, IsOk());

  // Create the server/client encryptor pair to use for verification.
  EncryptionKeyProvider key_provider(std::move(*key_pair));
  absl::StatusOr<std::unique_ptr<ClientEncryptor>> client_encryptor =
      ClientEncryptor::Create(attestation_results->encryption_public_key());
  ASSERT_THAT(client_encryptor, IsOk());
  ServerEncryptor server_encryptor(key_provider);

  // Verify client messages are decrypted by server.
  absl::StatusOr<EncryptedRequest> encrypted_client_msg =
      (*client_encryptor)->Encrypt("Hello Server", "");
  ASSERT_THAT(encrypted_client_msg, IsOk());
  absl::StatusOr<DecryptionResult> decrypted_client_msg =
      server_encryptor.Decrypt(*encrypted_client_msg);
  ASSERT_THAT(decrypted_client_msg, IsOk());
  EXPECT_EQ(decrypted_client_msg->plaintext, "Hello Server");

  // Verify server messages are decrypted by client.
  absl::StatusOr<EncryptedResponse> encrypted_server_msg =
      server_encryptor.Encrypt("Hello Client", "");
  ASSERT_THAT(encrypted_server_msg, IsOk());
  absl::StatusOr<DecryptionResult> decrypted_server_msg =
      (*client_encryptor)->Decrypt(*encrypted_server_msg);
  ASSERT_THAT(decrypted_server_msg, IsOk());
  EXPECT_EQ(decrypted_server_msg->plaintext, "Hello Client");
}
}  // namespace

}  // namespace oak::containers::sdk::standalone
