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

use jwt::{algorithm::AlgorithmType, header::JoseHeader};
use serde::Deserialize;

pub(crate) mod algorithm;

/// Partial view of a JWT header with the fields interesting for the validation
/// of the PKI flavour of Confidential Space JWT tokens.
///
/// https://cloud.google.com/confidential-computing/confidential-space/docs/connect-external-resources#attestation_token_structure
#[derive(Deserialize, PartialEq, Debug)]
pub struct Header {
    /// The algorithm used to sign the JWT.
    ///
    /// https://datatracker.ietf.org/doc/html/rfc7517#section-4.4
    #[serde(rename = "alg")]
    pub algorithm: AlgorithmType,

    /// The x509 chain of the certificate used to sign the JWT.
    ///
    /// https://datatracker.ietf.org/doc/html/rfc7517#section-4.7
    #[serde(rename = "x5c")]
    pub x509_chain: Vec<String>,
}

impl JoseHeader for Header {
    fn algorithm_type(&self) -> AlgorithmType {
        self.algorithm
    }
}
