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

#include "absl/base/thread_annotations.h"
#include "absl/synchronization/mutex.h"
#include "absl/types/span.h"
#include "oak/proto/node.grpc.pb.h"
#include "src/interp/interp.h"

namespace oak {

class OakNode final : public ::oak::Node::Service {
 public:
  OakNode(const std::string& node_id, const std::string& module);

  // Performs an Oak Module invocation.
  ::grpc::Status ProcessModuleCall(::grpc::GenericServerContext* context,
                                   const std::vector<uint8_t>& request_data,
                                   std::vector<uint8_t>* response_data)
      LOCKS_EXCLUDED(module_data_mutex_);

 private:
  ::grpc::Status GetAttestation(::grpc::ServerContext* context,
                                const ::oak::GetAttestationRequest* request,
                                ::oak::GetAttestationResponse* response) override;

  void InitEnvironment(wabt::interp::Environment* env);

  // Native implementation of the `oak.read_method_name` host function.
  ::wabt::interp::HostFunc::Callback OakReadMethodName(wabt::interp::Environment* env);

  // Native implementation of the `oak.read` host function.
  ::wabt::interp::HostFunc::Callback OakRead(::wabt::interp::Environment* env)
      EXCLUSIVE_LOCKS_REQUIRED(module_data_mutex_);

  // Native implementation of the `oak.write` host function.
  ::wabt::interp::HostFunc::Callback OakWrite(::wabt::interp::Environment* env)
      EXCLUSIVE_LOCKS_REQUIRED(module_data_mutex_);

  wabt::interp::Environment env_;
  // TODO: Use smart pointers.
  wabt::interp::DefinedModule* module_;

  // Incoming gRPC data for the current invocation.
  const ::grpc::GenericServerContext* server_context_;

  // Guards data used by OakRead and OakWrite host methods.
  ::absl::Mutex module_data_mutex_;

  // Span containing the gRPC request data passed to ProcessModuleCall.
  // This is a view of the data which advances each time the OakRead host function is called.
  ::absl::Span<const uint8_t> GUARDED_BY(module_data_mutex_) module_data_input_;

  // Pointer to the gRPC response data passed to ProcessModuleCall.
  // Data is inserted each time the OakWrite host function is called.
  std::vector<uint8_t>* GUARDED_BY(module_data_mutex_) module_data_output_;

  // Unique ID of the Oak Node instance. Creating multiple Oak Nodes with the same module and policy
  // configuration will result in Oak Node instances with distinct node_id_.
  const std::string node_id_;

  // Hash of the Oak Module with which this Oak Node was initialized.
  // To be used as the basis for remote attestation based on code identity.
  const std::string module_hash_sha_256_;
};

}  // namespace oak

#endif  // OAK_SERVER_OAK_NODE_H_
