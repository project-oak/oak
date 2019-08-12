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

#ifndef OAK_SERVER_STORAGE_MANAGER_H_
#define OAK_SERVER_STORAGE_MANAGER_H_

#include <string>

#include "absl/types/span.h"

namespace oak {

class StorageManager {
 public:
  StorageManager();

  absl::Span<const char> ReadResponseData(uint32_t size) {
    absl::Span<const char> response_data = operation_response_view_->subspan(0, size);
    operation_response_view_->remove_prefix(response_data.size());
    return response_data;
  }

  void WriteResponseData(std::string& response_data) {
    operation_response_data_ = response_data;
    operation_response_view_ =
        absl::Span<const char>(operation_response_data_.data(), operation_response_data_.size());
  }

 private:
  // The serialized StorageOperationResponse message set by WriteResponseData.
  std::string operation_response_data_;

  // A view of the response which advances each time the ReadResponseData method is called.
  absl::Span<const char> operation_response_view_;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_MANAGER_H_
