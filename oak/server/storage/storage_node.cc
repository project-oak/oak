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

#include "oak/server/storage/storage_node.h"

#include "absl/memory/memory.h"
#include "absl/strings/escaping.h"
#include "asylo/util/cleansing_types.h"
#include "asylo/util/logging.h"
#include "grpcpp/create_channel.h"
#include "oak/common/app_config.h"
#include "oak/proto/storage_channel.pb.h"

namespace oak {

constexpr size_t kMaxMessageSize = 1 << 16;

static std::string GetStorageId(const std::string& storage_name) {
  // TODO: Generate name-based UUID.
  return storage_name;
}

static asylo::CleansingVector<uint8_t> GetStorageEncryptionKey(const std::string& storage_name) {
  // TODO: Request encryption key from escrow service.
  std::string encryption_key =
      absl::HexStringToBytes("c0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedeadc0dedead");
  return asylo::CleansingVector<uint8_t>(encryption_key.begin(), encryption_key.end());
}

StorageNode::StorageNode(const std::string& name, const std::string& storage_address)
    : NodeThread(name),
      fixed_nonce_generator_(new oak::FixedNonceGenerator()),
      datum_name_cryptor_(kMaxMessageSize, fixed_nonce_generator_),
      datum_value_cryptor_(kMaxMessageSize, new asylo::AesGcmSivNonceGenerator()) {
  storage_service_ = oak::Storage::NewStub(
      grpc::CreateChannel(storage_address, grpc::InsecureChannelCredentials()));
}

const asylo::StatusOr<std::string> StorageNode::EncryptDatum(const std::string& datum,
                                                             DatumType datum_type) {
  // TODO: Replace "foo" with identifier for the encryption key.
  asylo::CleansingVector<uint8_t> key = GetStorageEncryptionKey("foo");
  asylo::CleansingString additional_authenticated_data;
  asylo::CleansingString nonce;
  asylo::CleansingString datum_encrypted;
  asylo::AesGcmSivCryptor* cryptor = nullptr;

  switch (datum_type) {
    case DatumType::NAME: {
      fixed_nonce_generator_->set_datum_name(datum);
      cryptor = &datum_name_cryptor_;
      break;
    };
    case DatumType::VALUE: {
      cryptor = &datum_value_cryptor_;
      break;
    };
  };
  // TODO: RETURN_IF_ERROR when one Status rules them all.
  asylo::Status status =
      cryptor->Seal(key, additional_authenticated_data, datum, &nonce, &datum_encrypted);
  if (!status.ok()) {
    return status;
  }

  return absl::StrCat(nonce, datum_encrypted);
}

const asylo::StatusOr<std::string> StorageNode::DecryptDatum(const std::string& input,
                                                             DatumType datum_type) {
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
  asylo::CleansingString datum_encrypted = input_clean.substr(kAesGcmSivNonceSize);
  asylo::CleansingString datum_decrypted;
  asylo::AesGcmSivCryptor* cryptor = nullptr;

  switch (datum_type) {
    case DatumType::NAME: {
      cryptor = &datum_name_cryptor_;
      break;
    };
    case DatumType::VALUE: {
      cryptor = &datum_value_cryptor_;
      break;
    };
  };
  // TODO: RETURN_IF_ERROR when one Status rules them all.
  asylo::Status status =
      cryptor->Open(key, additional_authenticated_data, datum_encrypted, nonce, &datum_decrypted);
  if (!status.ok()) {
    return status;
  }

  return std::string(datum_decrypted.data(), datum_decrypted.size());
}

void StorageNode::Run() {
  // Borrow pointers to the relevant channel halves.
  Handle request_handle = FindChannel(kStorageNodeRequestPortName);
  Handle response_handle = FindChannel(kStorageNodeResponsePortName);
  MessageChannelReadHalf* request_channel = BorrowReadChannel(request_handle);
  MessageChannelWriteHalf* response_channel = BorrowWriteChannel(response_handle);
  if (request_channel == nullptr || response_channel == nullptr) {
    LOG(ERROR) << "Required channel not available; handles: " << request_handle << ", "
               << response_handle;
  }
  std::vector<std::unique_ptr<ChannelStatus>> channel_status;
  channel_status.push_back(absl::make_unique<ChannelStatus>(request_handle));
  while (true) {
    if (!WaitOnChannels(&channel_status)) {
      LOG(WARNING) << "Node termination requested";
      return;
    }

    ReadResult result = request_channel->Read(INT_MAX, INT_MAX);
    if (result.required_size > 0) {
      LOG(ERROR) << "Message size too large: " << result.required_size;
      return;
    }

    StorageChannelRequest channel_request;
    channel_request.ParseFromString(std::string(result.msg->data.data(), result.msg->data.size()));
    // Any channel references included with the message will be dropped.

    // Forward the request to the storage service.
    grpc::Status status;
    grpc::ClientContext context;
    StorageChannelResponse channel_response;
    switch (channel_request.operation_case()) {
      case StorageChannelRequest::kReadRequest: {
        StorageReadRequest read_request;
        read_request.set_storage_id(GetStorageId(channel_request.storage_name()));
        read_request.set_transaction_id(channel_request.read_request().transaction_id());

        // TODO: Propagate error status.
        asylo::StatusOr<std::string> name_or =
            EncryptDatum(channel_request.read_request().datum_name(), DatumType::NAME);
        read_request.set_datum_name(name_or.ValueOrDie());

        StorageReadResponse read_response;
        status = storage_service_->Read(&context, read_request, &read_response);
        if (status.ok()) {
          // TODO: Propagate error status.
          asylo::StatusOr<std::string> value_or =
              DecryptDatum(read_response.datum_value(), DatumType::VALUE);
          channel_response.mutable_read_response()->set_datum_value(value_or.ValueOrDie());
        }
        break;
      }
      case StorageChannelRequest::kWriteRequest: {
        StorageWriteRequest write_request;
        write_request.set_storage_id(GetStorageId(channel_request.storage_name()));
        write_request.set_transaction_id(channel_request.write_request().transaction_id());

        // TODO: Propagate error status.
        asylo::StatusOr<std::string> name_or =
            EncryptDatum(channel_request.write_request().datum_name(), DatumType::NAME);
        write_request.set_datum_name(name_or.ValueOrDie());

        // TODO: Propagate error status.
        asylo::StatusOr<std::string> value_or =
            EncryptDatum(channel_request.write_request().datum_value(), DatumType::VALUE);
        write_request.set_datum_value(value_or.ValueOrDie());

        StorageWriteResponse write_response;
        status = storage_service_->Write(&context, write_request, &write_response);
        break;
      }
      case StorageChannelRequest::kDeleteRequest: {
        StorageDeleteRequest delete_request;
        delete_request.set_storage_id(GetStorageId(channel_request.storage_name()));
        delete_request.set_transaction_id(channel_request.delete_request().transaction_id());

        // TODO: Propagate error status.
        asylo::StatusOr<std::string> name_or =
            EncryptDatum(channel_request.delete_request().datum_name(), DatumType::NAME);
        delete_request.set_datum_name(name_or.ValueOrDie());

        StorageDeleteResponse delete_response;
        status = storage_service_->Delete(&context, delete_request, &delete_response);
        break;
      }
      case StorageChannelRequest::kBeginRequest: {
        StorageBeginRequest begin_request;
        begin_request.set_storage_id(GetStorageId(channel_request.storage_name()));

        StorageBeginResponse begin_response;
        status = storage_service_->Begin(&context, begin_request, &begin_response);
        if (status.ok()) {
          channel_response.mutable_begin_response()->set_transaction_id(
              begin_response.transaction_id());
        }
        break;
      }
      case StorageChannelRequest::kCommitRequest: {
        StorageCommitRequest commit_request;
        commit_request.set_storage_id(GetStorageId(channel_request.storage_name()));
        commit_request.set_transaction_id(channel_request.commit_request().transaction_id());

        StorageCommitResponse commit_response;
        status = storage_service_->Commit(&context, commit_request, &commit_response);
        break;
      }
      case StorageChannelRequest::kRollbackRequest: {
        StorageRollbackRequest rollback_request;
        rollback_request.set_storage_id(GetStorageId(channel_request.storage_name()));
        rollback_request.set_transaction_id(channel_request.rollback_request().transaction_id());

        StorageRollbackResponse rollback_response;
        status = storage_service_->Rollback(&context, rollback_request, &rollback_response);
        break;
      }
      case StorageChannelRequest::OPERATION_NOT_SET: {
        LOG(ERROR) << "unknown operation";
        status =
            grpc::Status(grpc::StatusCode::INVALID_ARGUMENT, "Operation request field not set.");
      }
    }
    if (!status.ok()) {
      LOG(ERROR) << "operation failed: " << status.error_code() << " " << status.error_message();
    }
    channel_response.mutable_status()->set_code(status.error_code());
    channel_response.mutable_status()->set_message(status.error_message());

    // Serialize the response and write it back to the Node's STORAGE_IN channel
    std::string response_data;
    channel_response.SerializeToString(&response_data);
    // TODO: figure out a way to avoid the extra copy (into then out of
    // std::string)
    std::unique_ptr<Message> response_message = absl::make_unique<Message>();
    response_message->data.insert(response_message->data.end(), response_data.begin(),
                                  response_data.end());
    response_channel->Write(std::move(response_message));
  }
}

}  // namespace oak
