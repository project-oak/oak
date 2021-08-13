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

//! Differential Privacy building blocks library based on the Go implementation at
//! https://github.com/google/differential-privacy/tree/main/go

pub mod checks;
pub mod noise;
pub mod rand;

/// Generic differential-privacy error.
#[derive(Debug)]
pub struct Error {
    msg: String,
}

/// Generic result type for the differential privacy crate.
pub type Result<T> = std::result::Result<T, Error>;

impl Error {
    pub fn new(msg: String) -> Self {
        Self { msg }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self.msg)
    }
}

impl From<::rand::Error> for Error {
    fn from(err: ::rand::Error) -> Self {
        Error::new(err.to_string())
    }
}
