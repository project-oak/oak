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

//! Checks for differentially private functions.
//!
//! Based on the upstream code at https://github.com/google/differential-privacy/blob/main/go/checks/checks.go

use crate::Error;

/// Returns an error if ε is +∞ or less than 2⁻⁵⁰.
pub fn check_epsilon_very_strict(label: &str, epsilon: f64) -> crate::Result<()> {
    if epsilon < (-50.0_f64).exp2() || epsilon.is_infinite() || epsilon.is_nan() {
        return Err(Error::new(format!(
            "{}: Epsilon is {}, should be at least 2^-50 (and cannot be infinity or NaN)",
            label, epsilon
        )));
    }
    Ok(())
}
/// Returns an error if δ is non-zero.
pub fn check_no_delta(label: &str, delta: f64) -> crate::Result<()> {
    if delta != 0.0 {
        return Err(Error::new(format!(
            "{}: Delta is {}, should be 0",
            label, delta
        )));
    }
    Ok(())
}

/// Returns an error if `l_0_sensitivity` is nonpositive.
pub fn check_l_0_sensitivity(label: &str, l_0_sensitivity: i64) -> crate::Result<()> {
    if l_0_sensitivity <= 0 {
        return Err(Error::new(format!(
            "{}: l_0_sensitivity is {}, should be strictly positive",
            label, l_0_sensitivity
        )));
    }
    Ok(())
}

/// Returns an error if `l_inf_sensitivity` is nonpositive or +∞.
pub fn check_l_inf_sensitivity(label: &str, l_inf_sensitivity: f64) -> crate::Result<()> {
    if l_inf_sensitivity <= 0.0 || l_inf_sensitivity.is_infinite() || l_inf_sensitivity.is_nan() {
        return Err(Error::new(format!(
          "{}: LInfSensitivity is {}, should be strictly positive (and cannot be infinity or NaN)",
          label, l_inf_sensitivity
        )));
    }
    Ok(())
}
