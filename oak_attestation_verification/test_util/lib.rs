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

/// Library with functions needed in both unit and integration tests. While it
/// is intended for tests, there are no restrictions on its use.
pub mod attestation_data;
pub mod endorsement_data;
mod factory;

pub use attestation_data::AttestationData;
pub use endorsement_data::EndorsementData;
pub use factory::{
    create_oc_endorsements, create_oc_reference_values,
    create_reference_values_for_extracted_evidence, create_rk_endorsements,
    create_rk_reference_values, extract_attestation_report, get_cb_reference_values,
    get_oc_reference_values, get_rk_reference_values,
};
