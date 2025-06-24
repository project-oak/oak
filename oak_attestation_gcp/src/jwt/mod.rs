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

/// Representation of a JWT token.
#[derive(Debug)]
pub struct Token {
    value: Vec<u8>,
}

impl Token {
    /// Returns the underlying token value as a slice of bytes.
    pub fn as_slice(&self) -> &[u8] {
        self.value.as_slice()
    }
}

impl From<String> for Token {
    fn from(raw: String) -> Self {
        Self { value: raw.into() }
    }
}

impl From<Vec<u8>> for Token {
    fn from(raw: Vec<u8>) -> Self {
        Self { value: raw }
    }
}
