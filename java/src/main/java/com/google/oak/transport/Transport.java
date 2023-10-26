//
// Copyright 2023 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

package com.google.oak.transport;

import com.google.oak.crypto.v1.EncryptedRequest;
import com.google.oak.crypto.v1.EncryptedResponse;
import com.google.oak.util.Result;

/** An interface for sending messages to the enclave. */
public interface Transport extends AutoCloseable {
  /**
   * Sends a request to the enclave and returns a response.
   *
   * @param encryptedRequest {@code oak.crypto.EncryptedRequest} proto message
   * @return {@code oak.crypto.EncryptedResponse} proto message wrapped in a {@code Result}
   */
  abstract Result<EncryptedResponse, String> invoke(EncryptedRequest encryptedRequest);
}
