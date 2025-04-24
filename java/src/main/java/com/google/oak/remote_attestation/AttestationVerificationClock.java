//
// Copyright 2025 The Project Oak Authors
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

package com.google.oak.remote_attestation;

/* A component that provides Java time to Rust attestation libraries.
 *
 * You can pass instances of this to constructors that build Rust-implemented
 * oak_session attestation components and require a Clock implementation.
 **/
public interface AttestationVerificationClock {
  long millisecondsSinceEpoch();
}
