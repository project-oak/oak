//
// Copyright 2024 The Project Oak Authors
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

use oak_attestation_explain::HumanReadableExplanation;
use oak_proto_rust::oak::attestation::v1::Evidence;
use prost::Message;

#[wasm_bindgen::prelude::wasm_bindgen]
pub fn explain(bytes: &[u8]) -> String {
    let extracted_evidence = {
        // TODO: b/334900893 - Generate extracted evidence programatically.
        let evidence = Evidence::decode(bytes).expect("could not decode evidence");
        oak_attestation_verification::verifier::extract_evidence(&evidence)
            .expect("could not extract evidence")
    };
    extracted_evidence.description().unwrap()
}
