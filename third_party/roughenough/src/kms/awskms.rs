// Copyright 2017-2019 int08h LLC
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

#[cfg(feature = "awskms")]
pub mod inner {
    extern crate bytes;

    use std::collections::HashMap;
    use std::default::Default;
    use std::fmt;
    use std::fmt::Formatter;
    use std::str::FromStr;

    use rusoto_core::Region;
    use rusoto_kms::{DecryptRequest, EncryptRequest, Kms, KmsClient};
    use bytes::Bytes;

    use crate::kms::{EncryptedDEK, KmsError, KmsProvider, PlaintextDEK, AD, DEK_SIZE_BYTES};

    /// Amazon Web Services Key Management Service
    /// https://aws.amazon.com/kms/
    pub struct AwsKms {
        kms_client: KmsClient,
        key_id: String,
    }

    impl AwsKms {
        /// Create a new instance from the full ARN of a AWS KMS key. The ARN is expected
        /// to be of the form `arn:aws:kms:some-aws-region:111122223333:key/1234abcd-12ab-34cd-56ef-1234567890ab`
        pub fn from_arn(arn: &str) -> Result<Self, KmsError> {
            let parts: Vec<&str> = arn.split(':').collect();

            if parts.len() != 6 {
                return Err(KmsError::InvalidConfiguration(format!(
                    "invalid KMS arn: too few parts {}",
                    parts.len()
                )));
            }

            let region_part = parts.get(3).expect("region is missing");
            let region = match Region::from_str(region_part) {
                Ok(r) => r,
                Err(e) => return Err(KmsError::InvalidConfiguration(e.to_string())),
            };

            Ok(AwsKms {
                kms_client: KmsClient::new(region),
                key_id: arn.to_string(),
            })
        }
    }

    impl KmsProvider for AwsKms {
        fn encrypt_dek(&self, plaintext_dek: &PlaintextDEK) -> Result<EncryptedDEK, KmsError> {
            if plaintext_dek.len() != DEK_SIZE_BYTES {
                return Err(KmsError::InvalidKey(format!(
                    "provided DEK wrong length: {}",
                    plaintext_dek.len()
                )));
            }

            let mut encrypt_req: EncryptRequest = Default::default();
            encrypt_req.key_id = self.key_id.clone();
            encrypt_req.plaintext = Bytes::from(plaintext_dek.as_slice());

            let mut enc_context = HashMap::new();
            enc_context.insert("AD".to_string(), AD.to_string());
            encrypt_req.encryption_context = Some(enc_context);

            match self.kms_client.encrypt(encrypt_req).sync() {
                Ok(result) => {
                    if let Some(ciphertext) = result.ciphertext_blob {
                        Ok(ciphertext.to_vec())
                    } else {
                        Err(KmsError::OperationFailed(
                            "no ciphertext despite successful response".to_string(),
                        ))
                    }
                }
                Err(e) => Err(KmsError::OperationFailed(e.to_string())),
            }
        }

        fn decrypt_dek(&self, encrypted_dek: &EncryptedDEK) -> Result<PlaintextDEK, KmsError> {
            let mut decrypt_req: DecryptRequest = Default::default();
            decrypt_req.ciphertext_blob = Bytes::from(encrypted_dek.as_slice());

            let mut dec_context = HashMap::new();
            dec_context.insert("AD".to_string(), AD.to_string());
            decrypt_req.encryption_context = Some(dec_context);

            match self.kms_client.decrypt(decrypt_req).sync() {
                Ok(result) => {
                    if let Some(plaintext_dek) = result.plaintext {
                        if plaintext_dek.len() == DEK_SIZE_BYTES {
                            Ok(plaintext_dek.to_vec())
                        } else {
                            Err(KmsError::InvalidKey(format!(
                                "decrypted DEK wrong length: {}",
                                plaintext_dek.len()
                            )))
                        }
                    } else {
                        Err(KmsError::OperationFailed(
                            "decrypted payload is empty".to_string(),
                        ))
                    }
                }
                Err(e) => Err(KmsError::OperationFailed(e.to_string())),
            }
        }
    }

    #[cfg(feature = "awskms")]
    impl fmt::Display for AwsKms {
        fn fmt(&self, f: &mut Formatter) -> fmt::Result {
            write!(f, "{}", self.key_id)
        }
    }
}
