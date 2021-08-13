//
// Copyright 2021 The Project Oak Authors
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

//! Methods to generate and add noise to data.
//!
//! Based on the upstream code at https://github.com/google/differential-privacy/blob/main/go/noise/noise.go

pub mod laplace_noise;
mod secure_noise_math;

/// Trait definition for primitives that add noise to data to make it differentially private.
pub trait Noise {
    /// Adds noise to the specified i64 `x` so that the output is ε-differentially private given the
    /// L_0 and L_∞ sensitivities of the database.
    fn add_noise_i64(
        &mut self,
        x: i64,
        l_0_sensitivity: i64,
        l_inf_sensitivity: i64,
        epsilon: f64,
        delta: f64,
    ) -> crate::Result<i64>;

    /// Adds noise to the specified f64 `x` so that the output is ε-differentially private given the
    /// L_0 and L_∞ sensitivities of the database.
    fn add_noise_f64(
        &mut self,
        x: f64,
        l_0_sensitivity: i64,
        l_inf_sensitivity: f64,
        epsilon: f64,
        delta: f64,
    ) -> crate::Result<f64>;
}
