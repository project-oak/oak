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

#include "absl/memory/memory.h"
#include "absl/strings/escaping.h"
#include "asylo/util/cleansing_types.h"
#include "asylo/util/logging.h"
#include "asylo/util/status_macros.h"
#include "grpcpp/create_channel.h"

namespace oak {

namespace {

constexpr size_t kMaxMessageSize = 1 << 16;

std::string GetStorageId(const std::string& storage_name) {
  // TODO: Generate name-based UUID.
  return storage_name;
}

asylo::CleansingVector<uint8_t> GetStorageEncryptionKey(const std::string& /*storage_name*/) {
  // TODO: Request encryption key from escrow service.
  std::string encryption_key =
      absl::HexStringToBytes("c0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedead");
  return asylo::CleansingVector<uint8_t>(encryption_key.begin(), encryption_key.end());
}

}  // namespace

StorageProcessor::StorageProcessor(const std::string& storage_address)
    : fixed_nonce_generator_(new oak::FixedNonceGenerator()),
      item_name_cryptor_(kMaxMessageSize, fixed_nonce_generator_),
      item_value_cryptor_(kMaxMessageSize, new asylo::AesGcmSivNonceGenerator()),
      storage_service_(oak::Storage::NewStub(
          grpc::CreateChannel(storage_address, grpc::InsecureChannelCredentials()))) {}

const asylo::StatusOr<std::string> StorageProcessor::EncryptItem(const std::string& item,
                                                                 ItemType item_type) {
  // TODO: Replace "foo" with identifier for the encryption key.
  asylo::CleansingVector<uint8_t> key = GetStorageEncryptionKey("foo");
  asylo::CleansingString additional_authenticated_data;
  asylo::CleansingString nonce;
  asylo::CleansingString item_encrypted;
  asylo::AesGcmSivCryptor* cryptor = nullptr;

  switch (item_type) {
    case ItemType::NAME: {
      fixed_nonce_generator_->set_item_name(item);
      cryptor = &item_name_cryptor_;
      break;
    };
    case ItemType::VALUE: {
      cryptor = &item_value_cryptor_;
      break;
    };
  };
  ASYLO_RETURN_IF_ERROR(
      cryptor->Seal(key, additional_authenticated_data, item, &nonce, &item_encrypted));

  return absl::StrCat(nonce, item_encrypted);
}

const asylo::StatusOr<std::string> StorageProcessor::DecryptItem(const std::string& input,
                                                                 ItemType item_type) {
  asylo::CleansingString input_clean(input.data(), input.size());

  if (input_clean.size() < kAesGcmSivNonceSize) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                         absl::StrCat("Input too short: expected at least ", kAesGcmSivNonceSize,
                                      " bytes, got ", input_clean.size()));
  }

  // TODO: Replace "foo" with identifier for the encryption key.
  asylo::CleansingVector<uint8_t> key(GetStorageEncryptionKey("foo"));
  asylo::CleansingString additional_authenticated_data;
  asylo::CleansingString nonce = input_clean.substr(0, kAesGcmSivNonceSize);
  asylo::CleansingString item_encrypted = input_clean.substr(kAesGcmSivNonceSize);
  asylo::CleansingString item_decrypted;
  asylo::AesGcmSivCryptor* cryptor = nullptr;

  switch (item_type) {
    case ItemType::NAME: {
      cryptor = &item_name_cryptor_;
      break;
    };
    case ItemType::VALUE: {
      cryptor = &item_value_cryptor_;
      break;
    };
  };
  ASYLO_RETURN_IF_ERROR(
      cryptor->Open(key, additional_authenticated_data, item_encrypted, nonce, &item_decrypted));

  return std::string(item_decrypted.data(), item_decrypted.size());
}

void StorageProcessor::Read(const std::string& storage_name, const std::string& item_name,
                            const std::string& transaction_id, std::string* item_value) {
  CHECK(item_value != nullptr);

  StorageReadRequest read_request;
  read_request.set_storage_id(GetStorageId(storage_name));
  if (!transaction_id.empty()) {
    read_request.set_transaction_id(transaction_id);
  }
  // TODO(650): Propagate error status.
  asylo::StatusOr<std::string> name_or = EncryptItem(item_name, ItemType::NAME);
  read_request.set_item_name(name_or.ValueOrDie());

  grpc::ClientContext context;
  StorageReadResponse read_response;
  grpc::Status status = storage_service_->Read(&context, read_request, &read_response);
  // TODO(650): Propagate error status.
  if (status.ok()) {
    asylo::StatusOr<std::string> value_or =
        DecryptItem(read_response.item_value(), ItemType::VALUE);
    *item_value = value_or.ValueOrDie();
  }
}

void StorageProcessor::Write(const std::string& storage_name, const std::string& item_name,
                             const std::string& item_value, const std::string& transaction_id) {
  StorageWriteRequest write_request;
  write_request.set_storage_id(GetStorageId(storage_name));
  if (!transaction_id.empty()) {
    write_request.set_transaction_id(transaction_id);
  }
  // TODO(650): Propagate error status.
  asylo::StatusOr<std::string> name_or = EncryptItem(item_name, ItemType::NAME);
  write_request.set_item_name(name_or.ValueOrDie());

  // TODO(650): Propagate error status.
  asylo::StatusOr<std::string> value_or = EncryptItem(item_value, ItemType::VALUE);
  write_request.set_item_value(value_or.ValueOrDie());

  grpc::ClientContext context;
  StorageWriteResponse write_response;
  grpc::Status status = storage_service_->Write(&context, write_request, &write_response);
}

void StorageProcessor::Delete(const std::string& storage_name, const std::string& item_name,
                              const std::string& transaction_id) {
  StorageDeleteRequest delete_request;
  delete_request.set_storage_id(GetStorageId(storage_name));
  if (!transaction_id.empty()) {
    delete_request.set_transaction_id(transaction_id);
  }
  // TODO(650): Propagate error status.
  asylo::StatusOr<std::string> name_or = EncryptItem(item_name, ItemType::NAME);
  delete_request.set_item_name(name_or.ValueOrDie());

  grpc::ClientContext context;
  StorageDeleteResponse delete_response;
  // TODO(#650): Propagate error status.
  grpc::Status status = storage_service_->Delete(&context, delete_request, &delete_response);
}

void StorageProcessor::Begin(const std::string& storage_name, std::string* transaction_id) {
  CHECK(transaction_id != nullptr);

  StorageBeginRequest begin_request;
  begin_request.set_storage_id(GetStorageId(storage_name));

  grpc::ClientContext context;
  StorageBeginResponse begin_response;
  // TODO(#650): Propagate error status.
  grpc::Status status = storage_service_->Begin(&context, begin_request, &begin_response);
  if (status.ok()) {
    *transaction_id = begin_response.transaction_id();
  }
}

void StorageProcessor::Commit(const std::string& storage_name, const std::string& transaction_id) {
  StorageCommitRequest commit_request;
  commit_request.set_storage_id(GetStorageId(storage_name));
  commit_request.set_transaction_id(transaction_id);

  grpc::ClientContext context;
  StorageCommitResponse commit_response;
  // TODO(#650): Propagate error status.
  grpc::Status status = storage_service_->Commit(&context, commit_request, &commit_response);
}

void StorageProcessor::Rollback(const std::string& storage_name,
                                const std::string& transaction_id) {
  StorageRollbackRequest rollback_request;
  rollback_request.set_storage_id(GetStorageId(storage_name));
  rollback_request.set_transaction_id(transaction_id);

  grpc::ClientContext context;
  StorageRollbackResponse rollback_response;
  // TODO(#650): Propagate error status.
  grpc::Status status = storage_service_->Rollback(&context, rollback_request, &rollback_response);
}

}  // namespace oak
