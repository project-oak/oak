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

mod cpuid;
mod mmio;

pub use cpuid::*;
pub use mmio::*;
pub use oak_stage0_dice::{
    mock_attestation_report as get_attestation, mock_derived_key as get_derived_key,
};
pub use x86_64::registers::model_specific::Msr;
