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

//! This module provides traits that allow to bind the data to the session.
use alloc::vec::Vec;

use anyhow::Error;
#[cfg(test)]
use mockall::automock;

// Trait that allows binding session to the arbitrary data
pub trait SessionBinder: Send {
    fn bind(&self, bound_data: &[u8]) -> Vec<u8>;
}

// Trait that allows verifying the binding between the session and the arbitrary
// data.
#[cfg_attr(test, automock)]
pub trait SessionBindingVerifier: Send {
    fn verify_binding(&self, bound_data: &[u8], binding: &[u8]) -> Result<(), Error>;
}
