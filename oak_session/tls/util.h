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
#ifndef OAK_SESSION_TLS_SSL_UTIL_H_
#define OAK_SESSION_TLS_SSL_UTIL_H_

#include "absl/status/status.h"
#include "absl/status/statusor.h"

namespace oak::session::tls::util {

absl::StatusOr<std::string> LoadPrivateKeyFromFile(const char* key_path);
absl::StatusOr<std::string> LoadCertificateFromFile(const char* cert_path);

}  // namespace oak::session::tls::util

#endif  // OAK_SESSION_TLS_SSL_UTIL_H__
