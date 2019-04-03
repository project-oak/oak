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

#ifndef OAK_SERVER_OAK_NODE_H_
#define OAK_SERVER_OAK_NODE_H_

#include "oak/proto/node.grpc.pb.h"

#include "src/interp/interp.h"

namespace oak {
namespace grpc_server {

class OakNode final : public ::oak::Node::Service {
 public:
  OakNode(const std::string& node_id, const std::string& module);

  ::grpc::Status HandleGrpcCall(const ::grpc::GenericServerContext* context,
                                const ::grpc::ByteBuffer* request_data,
                                ::grpc::ByteBuffer* response_data);

 private:
  ::grpc::Status GetAttestation(::grpc::ServerContext* context,
                                const ::oak::GetAttestationRequest* request,
                                ::oak::GetAttestationResponse* response) override;

  void InitEnvironment(wabt::interp::Environment* env);

  // Native implementation of the `oak.read_method_name` host function.
  ::wabt::interp::HostFunc::Callback OakReadMethodName(wabt::interp::Environment* env);

  // Native implementation of the `oak.read` host function.
  ::wabt::interp::HostFunc::Callback OakRead(wabt::interp::Environment* env);

  // Native implementation of the `oak.write` host function.
  ::wabt::interp::HostFunc::Callback OakWrite(wabt::interp::Environment* env);

  wabt::interp::Environment env_;
  // TODO: Use smart pointers.
  wabt::interp::DefinedModule* module_;

  // Incoming gRPC data for the current invocation.
  const ::grpc::GenericServerContext* server_context_;

  std::unique_ptr<std::vector<char>> request_data_;
  // Cursor keeping track of how many bytes of request_data_ have been consumed by the Oak Module
  // during the current invocation.
  uint32_t request_data_cursor_;

  // Outgoing gRPC data for the current invocation.
  std::unique_ptr<std::vector<char>> response_data_;

  // Unique ID of the Oak Node instance. Creating multiple Oak Nodes with the same module and policy
  // configuration will result in Oak Node instances with distinct node_id_.
  const std::string node_id_;

  // Hash of the Oak Module with which this Oak Node was initialized.
  // To be used as the basis for remote attestation based on code identity.
  const std::string module_hash_sha_256_;
};

}  // namespace grpc_server
}  // namespace oak

#endif  // OAK_SERVER_OAK_NODE_H_
