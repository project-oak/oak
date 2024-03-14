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

import com.google.oak.session.v1.EndorsedEvidence;
import com.google.oak.util.Result;

/** An interface for providing an enclave evidence. */
public interface EvidenceProvider {
  /**
   * Returns evidence about the trustworthiness of a remote server.
   *
   * @return {@code EndorsedEvidence} wrapped in a {@code Result}
   */
  abstract Result<EndorsedEvidence, String> getEndorsedEvidence();
}
