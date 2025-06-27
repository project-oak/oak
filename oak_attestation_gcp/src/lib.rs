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

pub mod attestation;
pub mod verification;

mod jwt;

#[cfg(test)]
mod tests {
    use std::fs;

    use googletest::prelude::*;
    use jwt::{Token, Unverified};
    use oak_file_utils::data_path;
    use serde_json::Value;
    use x509_cert::{der::DecodePem, Certificate};

    use crate::{
        jwt::Header,
        verification::{verify_attestation_token, AttestationVerificationError},
    };

    #[test]
    fn validate_token_ok() -> Result<()> {
        let token_str = read_testdata("valid.jwt");
        let root = Certificate::from_pem(read_testdata("root.crt"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Value, Unverified> =
            Token::parse_unverified(&token_str)?;

        verify_attestation_token(unverified_token, &root)?;

        Ok(())
    }

    #[test]
    fn validate_token_invalid_signature() -> Result<()> {
        let token_str = read_testdata("invalid_signature.jwt");
        let root = Certificate::from_pem(read_testdata("root.crt"))
            .expect("Failed to parse root certificate");

        let unverified_token: Token<Header, Value, Unverified> =
            Token::parse_unverified(&token_str)?;

        assert_that!(
            unsafe { verify_attestation_token(unverified_token, &root).unwrap_err_unchecked() },
            matches_pattern!(AttestationVerificationError::JWTError(matches_pattern!(
                jwt::Error::InvalidSignature
            )))
        );

        Ok(())
    }

    fn read_testdata(file: &str) -> String {
        fs::read_to_string(data_path(format!("oak_attestation_gcp/testdata/{file}"))).unwrap()
    }
}
