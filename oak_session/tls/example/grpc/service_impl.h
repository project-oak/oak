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

#ifndef OAK_EXPERIMENTS_TLS_OVER_GRPC_SERVICE_IMPL_H_
#define OAK_EXPERIMENTS_TLS_OVER_GRPC_SERVICE_IMPL_H_

#include <memory>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "grpcpp/grpcpp.h"
#include "oak_session/tls/example/grpc/service.grpc.pb.h"
#include "oak_session/tls/oak_session_tls.h"
#include "openssl/base.h"
#include "openssl/bio.h"
#include "openssl/ssl.h"

namespace oak::session::tls::example {

class TlsOverGrpcServiceImpl final : public TlsOverGrpc::Service {
 public:
  static absl::StatusOr<std::unique_ptr<TlsOverGrpcServiceImpl>> Create(
      const std::string& server_key_asn1, const std::string& server_cert_asn1,
      const std::string& client_cert_path);
  grpc::Status TlsSession(
      grpc::ServerContext* context,
      grpc::ServerReaderWriter<TlsSessionResponse, TlsSessionRequest>* stream)
      override;

 private:
  TlsOverGrpcServiceImpl(std::unique_ptr<OakSessionTlsContext> context);
  std::unique_ptr<OakSessionTlsContext> context_;
};

}  // namespace oak::session::tls::example

#endif  // OAK_EXPERIMENTS_TLS_OVER_GRPC_SERVICE_IMPL_H_
