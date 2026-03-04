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

//! Core types for the falsify framework.
//!
//! This `no_std` crate defines the [`Claim`] trait and [`Evaluation`] enum
//! shared across native and Wasm runners, and by individual claim
//! implementations.

#![no_std]

extern crate alloc;

use alloc::boxed::Box;

/// The result of evaluating a claim against a specific input.
#[derive(Debug, PartialEq, Eq)]
pub enum Evaluation {
    /// The claim held successfully for this input.
    Intact,
    /// The input falsified the claim (a counterexample was found).
    Falsified,
}

/// Wire encoding: [`Evaluation::Intact`].
pub const EVALUATION_INTACT: u8 = 0x00;
/// Wire encoding: [`Evaluation::Falsified`].
pub const EVALUATION_FALSIFIED: u8 = 0x01;

impl Evaluation {
    /// Encodes the evaluation as a single byte.
    pub fn to_byte(&self) -> u8 {
        match self {
            Self::Intact => EVALUATION_INTACT,
            Self::Falsified => EVALUATION_FALSIFIED,
        }
    }

    /// Decodes an evaluation from a single byte.
    ///
    /// Returns `None` for unrecognised values.
    pub fn from_byte(b: u8) -> Option<Self> {
        match b {
            EVALUATION_INTACT => Some(Self::Intact),
            EVALUATION_FALSIFIED => Some(Self::Falsified),
            _ => None,
        }
    }
}

/// A claim that can be evaluated against a byte payload.
pub trait Claim {
    /// Evaluates the claim against the provided input bytes.
    ///
    /// - `Ok(Evaluation::Intact)`: The claim holds for this input.
    /// - `Ok(Evaluation::Falsified)`: The claim is falsified by this input (a
    ///   counterexample was found).
    /// - `Err(e)`: An exception occurred, the result is inconclusive.
    fn evaluate(&self, input: &[u8]) -> Result<Evaluation, Box<dyn core::error::Error>>;
}
