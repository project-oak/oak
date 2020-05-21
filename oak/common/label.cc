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

#include "oak/common/label.h"

#include "absl/strings/escaping.h"

namespace oak {

// The `-bin` suffix allows sending binary data for this metadata key.
//
// See https://github.com/grpc/grpc/blob/master/doc/PROTOCOL-HTTP2.md.
const char kOakLabelGrpcMetadataKey[] = "x-oak-label-bin";

// The `-bin` suffix allows sending binary data for this metadata key.
//
// See https://github.com/grpc/grpc/blob/master/doc/PROTOCOL-HTTP2.md.
const char kOakAuthorizationBearerTokenGrpcMetadataKey[] = "x-oak-authorization-bearer-token-bin";

std::string SerializeLabel(const oak::label::Label& label_proto) {
  return label_proto.SerializeAsString();
}

oak::label::Label DeserializeLabel(const std::string& label_bytes) {
  oak::label::Label label_proto;
  // TODO(#488): Check errors.
  label_proto.ParseFromString(label_bytes);
  return label_proto;
}

oak::label::Label AuthorizationBearerTokenLabel(const std::string& authorization_token_hmac) {
  oak::label::Label label;
  auto* confidentiality_tag = label.add_confidentiality_tags();
  auto* integrity_tag = label.add_integrity_tags();
  confidentiality_tag->mutable_grpc_tag()->set_authorization_bearer_token_hmac(
      authorization_token_hmac);
  // We set integrity tag here, even though it would make more sense for the server to determine
  // what integrity tag to assign to the incoming message, based on the authentication mechanism
  // used (e.g. the actual bearer token, rather than its HMAC).
  // Partly tracked in #420.
  integrity_tag->mutable_grpc_tag()->set_authorization_bearer_token_hmac(authorization_token_hmac);
  return label;
}

oak::label::Label WebAssemblyModuleAttestationLabel(const std::string& module_attestation) {
  oak::label::Label label;
  auto* confidentiality_tag = label.add_confidentiality_tags();
  auto* integrity_tag = label.add_integrity_tags();
  confidentiality_tag->mutable_web_assembly_module_tag()->set_module_attestation(
      module_attestation);
  integrity_tag->mutable_web_assembly_module_tag()->set_module_attestation(module_attestation);
  return label;
}

}  // namespace oak
