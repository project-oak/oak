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

#ifndef OAK_COMMON_LABEL_H_
#define OAK_COMMON_LABEL_H_

#include "absl/base/attributes.h"
#include "oak_abi/proto/label.pb.h"

namespace oak {

// Metadata key used to refer to the Oak Label associated with the gRPC request. This is
// effectively treated as the name of a custom HTTP header.
ABSL_CONST_INIT extern const char kOakLabelGrpcMetadataKey[];

// Serialized the provided label so that it can be sent as a binary gRPC metadata value.
std::string SerializeLabel(const oak::label::Label& label_proto);

// Deserializes the provided binary gRPC metadata value into a label.
oak::label::Label DeserializeLabel(const std::string& label_bytes);

// Creates a label having as principal the provided WebAssembly module SHA-256 hash.
oak::label::Label WebAssemblyModuleHashLabel(const std::string& web_asesemblymodule_hash_sha_256);

// Creates a label having as principal the provided WebAssembly module Ed25519 public key.
// https://ed25519.cr.yp.to
oak::label::Label WebAssemblyModuleSignatureLabel(
    const std::string& web_assembly_module_public_key);

// Creates a label having as principal the provided TLS authority (host:port).
oak::label::Label TlsEndpointLabel(const std::string& authority);

// Creates a label having as principal the provided public key identity.
oak::label::Label PublicKeyIdentityLabel(const std::string& public_key_identity);

// Creates a public untrusted label, which is the least confidential and least trusted label and
// applies no confidentiality restrictions to the data contained in the request.
oak::label::Label PublicUntrustedLabel();

}  // namespace oak

#endif  // OAK_COMMON_LABEL_H_
