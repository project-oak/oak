/*
 *
 * Copyright 2018 Asylo authors
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
 *
 */

#ifndef ASYLO_UTIL_CLEANUP_H_
#define ASYLO_UTIL_CLEANUP_H_

#include <functional>
#include <utility>

namespace asylo {

// A cleanup utility. Takes a function in its constructor and calls that
// function in its destructor.
//
// Example usage:
//
//     StatusOr<string> ReadNBytesOrFail(absl::string_view &file_name,
//                                       size_t num_bytes) {
//       int fd =
//           open(string(file_name.data(), file_name.size()).data(), O_RDONLY);
//       if (fd == -1) {
//         return Status(static_cast<error::PosixError>(errno),
//                       absl::StrCat("Failed to open file ", file_name));
//       }
//
//       // Create a Cleanup object to close the file here. This ensures that
//       // the file is closed no matter the path of execution.
//       Cleanup close_fd([fd]() { close(fd); });
//
//       string read_buf(num_bytes + 1);
//       ssize_t read_result =
//           read(fd, const_cast<char *>(read_buf.data()), num_bytes);
//       if (read_result == -1) {
//         return Status(static_cast<error::PosixError>(errno),
//                       absl::StrCat("Failed to read file ", file_name));
//       } else if (read_result < num_bytes) {
//         return Status(error::GoogleError::INVALID_ARGUMENT,
//                       absl::StrCat("Could not read ", num_bytes,
//                                    " bytes from ", file_name));
//       }
//
//       return read_buf;
//     }
//
class Cleanup {
 public:
  Cleanup() : cleanup_function_() {}

  explicit Cleanup(std::function<void()> cleanup_function)
      : cleanup_function_(std::move(cleanup_function)) {}

  Cleanup(const Cleanup &other) = delete;
  Cleanup &operator=(const Cleanup &other) = delete;

  Cleanup(Cleanup &&other) = delete;
  Cleanup &operator=(Cleanup &&other) = delete;

  ~Cleanup() {
    if (cleanup_function_) {
      cleanup_function_();
    }
  }

  // Releases the contained cleanup function so that it is not called when this
  // object is destroyed. Returns the cleanup function.
  std::function<void()> release() {
    auto ret = std::move(cleanup_function_);
    cleanup_function_ = nullptr;
    return ret;
  }

 private:
  std::function<void()> cleanup_function_;
};

}  // namespace asylo

#endif  // ASYLO_UTIL_CLEANUP_H_
