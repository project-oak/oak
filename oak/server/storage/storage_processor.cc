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

#include "oak/server/storage/storage_processor.h"

#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/sha.h>

#include <algorithm>
#include <array>

#include "absl/memory/memory.h"
#include "absl/strings/escaping.h"
#include "grpcpp/create_channel.h"
#include "oak/common/logging.h"
#include "third_party/asylo/status_macros.h"

namespace oak {

namespace {

constexpr size_t kMaxMessageSize = 1 << 16;

absl::Status FromGrpcStatus(grpc::Status grpc_status) {
  return absl::Status(static_cast<absl::StatusCode>(grpc_status.error_code()),
                      grpc_status.error_message());
}

// If a gRPC client method returns a grpc::Status error, convert it to an
// absl::Status and return it.
#define RETURN_IF_GRPC_ERROR(expr)                          \
  do {                                                      \
    auto _grpc_status_to_verify = (expr);                   \
    if (ABSL_PREDICT_FALSE(!_grpc_status_to_verify.ok())) { \
      return FromGrpcStatus(_grpc_status_to_verify);        \
    }                                                       \
  } while (false)

std::string GetStorageId(const std::string& storage_name) {
  // TODO: Generate name-based UUID.
  return storage_name;
}

std::vector<uint8_t> GetStorageEncryptionKey(const std::string& /*storage_name*/) {
  // TODO: Request encryption key from escrow service.
  std::string encryption_key =
      absl::HexStringToBytes("c0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedead");
  return std::vector<uint8_t>(encryption_key.begin(), encryption_key.end());
}

constexpr size_t kAesGcmSivNonceSize = 12;

/// A 96-bit nonce generator that returns a uniformly distributed random nonce.
absl::Status RandomNonce(std::array<uint8_t, kAesGcmSivNonceSize>* nonce) {
  if (RAND_bytes(nonce->data(), nonce->size()) != 1) {
    return absl::Status(absl::StatusCode::kInternal, "RAND_bytes failed");
  }
  return absl::OkStatus();
}

// Produces fixed nonces using the storage encryption key and item name to
// allow deterministic encryption of the item name.
absl::Status DeterministicNonce(const std::vector<uint8_t>& key_id, const std::string& item_name,
                                std::array<uint8_t, kAesGcmSivNonceSize>* nonce) {
  // Generates a digest of the inputs to extract a fixed-size nonce.
  SHA256_CTX context;
  SHA256_Init(&context);
  SHA256_Update(&context, item_name.data(), item_name.size());
  SHA256_Update(&context, key_id.data(), key_id.size());
  std::vector<uint8_t> digest(SHA256_DIGEST_LENGTH);
  SHA256_Final(digest.data(), &context);
  std::copy_n(digest.begin(), kAesGcmSivNonceSize, nonce->begin());

  return absl::OkStatus();
}

}  // namespace

StorageProcessor::StorageProcessor(const std::string& storage_address)
    : storage_service_(oak::Storage::NewStub(
          grpc::CreateChannel(storage_address, grpc::InsecureChannelCredentials()))) {}

const oak::StatusOr<std::string> StorageProcessor::EncryptItem(const std::string& plaintext,
                                                               ItemType item_type) {
  // TODO: Replace "foo" with identifier for the encryption key.
  std::vector<uint8_t> key = GetStorageEncryptionKey("foo");
  std::vector<uint8_t> additional_data;
  std::vector<uint8_t> ciphertext;

  std::array<uint8_t, kAesGcmSivNonceSize> nonce;
  switch (item_type) {
    case ItemType::NAME: {
      std::vector<uint8_t> key_id(SHA256_DIGEST_LENGTH);
      SHA256(key.data(), key.size(), key_id.data());
      OAK_RETURN_IF_ERROR(DeterministicNonce(key_id, plaintext, &nonce));
      break;
    }
    case ItemType::VALUE:
      OAK_RETURN_IF_ERROR(RandomNonce(&nonce));
      break;
  }

  if (additional_data.size() + plaintext.size() > kMaxMessageSize) {
    return absl::Status(absl::StatusCode::kInvalidArgument, "Message size is too large");
  }

  // Initialize the AEAD context.
  EVP_AEAD const* const aead = EVP_aead_aes_256_gcm_siv();
  EVP_AEAD_CTX context;
  if (EVP_AEAD_CTX_init(&context, aead, key.data(), key.size(), EVP_AEAD_max_tag_len(aead),
                        nullptr) != 1) {
    return absl::Status(absl::StatusCode::kInternal, "EVP_AEAD_CTX_init failed");
  }

  // Create temporary storage for generating the ciphertext.
  size_t max_ciphertext_length = plaintext.size() + EVP_AEAD_max_overhead(aead);
  ciphertext.resize(max_ciphertext_length);

  // Perform actual encryption.
  size_t ciphertext_length = 0;
  if (EVP_AEAD_CTX_seal(
          &context, ciphertext.data(), &ciphertext_length, ciphertext.size(), nonce.data(),
          nonce.size(), reinterpret_cast<const uint8_t*>(plaintext.data()), plaintext.size(),
          reinterpret_cast<const uint8_t*>(additional_data.data()), additional_data.size()) != 1) {
    EVP_AEAD_CTX_cleanup(&context);
    return absl::Status(absl::StatusCode::kInternal, "EVP_AEAD_CTX_seal failed");
  }
  ciphertext.resize(ciphertext_length);

  EVP_AEAD_CTX_cleanup(&context);
  std::string result(nonce.begin(), nonce.end());
  result.insert(result.end(), ciphertext.begin(), ciphertext.end());
  return result;
}

const oak::StatusOr<std::string> StorageProcessor::DecryptItem(const std::string& input, ItemType) {
  if (input.size() < kAesGcmSivNonceSize) {
    return absl::Status(absl::StatusCode::kInvalidArgument,
                        absl::StrCat("Input too short: expected at least ", kAesGcmSivNonceSize,
                                     " bytes, got ", input.size()));
  }

  // TODO: Replace "foo" with identifier for the encryption key.
  std::vector<uint8_t> key = GetStorageEncryptionKey("foo");
  std::vector<uint8_t> additional_data;
  std::vector<uint8_t> nonce(input.begin(), input.begin() + kAesGcmSivNonceSize);
  std::vector<uint8_t> ciphertext(input.begin() + kAesGcmSivNonceSize, input.end());
  // TODO: use a cleansing RAII type for the plaintext.
  std::vector<uint8_t> plaintext;
  plaintext.resize(ciphertext.size());

  // Initialize the AEAD context.
  EVP_AEAD const* const aead = EVP_aead_aes_256_gcm_siv();
  EVP_AEAD_CTX context;
  if (EVP_AEAD_CTX_init(&context, aead, key.data(), key.size(), EVP_AEAD_max_tag_len(aead),
                        nullptr) != 1) {
    return absl::Status(absl::StatusCode::kInternal, "EVP_AEAD_CTX_init failed");
  }

  // Perform the actual decryption.
  size_t plaintext_length = 0;
  if (EVP_AEAD_CTX_open(&context, plaintext.data(), &plaintext_length, plaintext.size(),
                        nonce.data(), nonce.size(), ciphertext.data(), ciphertext.size(),
                        additional_data.data(), additional_data.size()) != 1) {
    EVP_AEAD_CTX_cleanup(&context);
    return absl::Status(absl::StatusCode::kInternal, "EVP_AEAD_CTX_open failed");
  }
  plaintext.resize(plaintext_length);

  EVP_AEAD_CTX_cleanup(&context);

  return std::string(plaintext.begin(), plaintext.end());
}

oak::StatusOr<std::string> StorageProcessor::Read(const std::string& storage_name,
                                                  const std::string& item_name,
                                                  const std::string& transaction_id) {
  StorageReadRequest read_request;
  read_request.set_storage_id(GetStorageId(storage_name));
  if (!transaction_id.empty()) {
    read_request.set_transaction_id(transaction_id);
  }
  std::string name;
  OAK_ASSIGN_OR_RETURN(name, EncryptItem(item_name, ItemType::NAME));
  read_request.set_item_name(name);

  grpc::ClientContext context;
  StorageReadResponse read_response;
  RETURN_IF_GRPC_ERROR(storage_service_->Read(&context, read_request, &read_response));
  return DecryptItem(read_response.item_value(), ItemType::VALUE);
}

absl::Status StorageProcessor::Write(const std::string& storage_name, const std::string& item_name,
                                     const std::string& item_value,
                                     const std::string& transaction_id) {
  StorageWriteRequest write_request;
  write_request.set_storage_id(GetStorageId(storage_name));
  if (!transaction_id.empty()) {
    write_request.set_transaction_id(transaction_id);
  }
  std::string name;
  OAK_ASSIGN_OR_RETURN(name, EncryptItem(item_name, ItemType::NAME));
  write_request.set_item_name(name);

  std::string value;
  OAK_ASSIGN_OR_RETURN(value, EncryptItem(item_value, ItemType::VALUE));
  write_request.set_item_value(value);

  grpc::ClientContext context;
  StorageWriteResponse write_response;
  return FromGrpcStatus(storage_service_->Write(&context, write_request, &write_response));
}

absl::Status StorageProcessor::Delete(const std::string& storage_name, const std::string& item_name,
                                      const std::string& transaction_id) {
  StorageDeleteRequest delete_request;
  delete_request.set_storage_id(GetStorageId(storage_name));
  if (!transaction_id.empty()) {
    delete_request.set_transaction_id(transaction_id);
  }
  std::string name;
  OAK_ASSIGN_OR_RETURN(name, EncryptItem(item_name, ItemType::NAME));
  delete_request.set_item_name(name);

  grpc::ClientContext context;
  StorageDeleteResponse delete_response;
  return FromGrpcStatus(storage_service_->Delete(&context, delete_request, &delete_response));
}

oak::StatusOr<std::string> StorageProcessor::Begin(const std::string& storage_name) {
  StorageBeginRequest begin_request;
  begin_request.set_storage_id(GetStorageId(storage_name));

  grpc::ClientContext context;
  StorageBeginResponse begin_response;
  RETURN_IF_GRPC_ERROR(storage_service_->Begin(&context, begin_request, &begin_response));
  return oak::StatusOr<std::string>(begin_response.transaction_id());
}

absl::Status StorageProcessor::Commit(const std::string& storage_name,
                                      const std::string& transaction_id) {
  StorageCommitRequest commit_request;
  commit_request.set_storage_id(GetStorageId(storage_name));
  commit_request.set_transaction_id(transaction_id);

  grpc::ClientContext context;
  StorageCommitResponse commit_response;
  return FromGrpcStatus(storage_service_->Commit(&context, commit_request, &commit_response));
}

absl::Status StorageProcessor::Rollback(const std::string& storage_name,
                                        const std::string& transaction_id) {
  StorageRollbackRequest rollback_request;
  rollback_request.set_storage_id(GetStorageId(storage_name));
  rollback_request.set_transaction_id(transaction_id);

  grpc::ClientContext context;
  StorageRollbackResponse rollback_response;
  return FromGrpcStatus(storage_service_->Rollback(&context, rollback_request, &rollback_response));
}

}  // namespace oak
