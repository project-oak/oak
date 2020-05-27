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

#[cfg(feature = "gcpkms")]
pub mod inner {
    extern crate base64;
    extern crate google_cloudkms1 as cloudkms1;
    extern crate hyper;
    extern crate hyper_rustls;
    extern crate yup_oauth2 as oauth2;

    use std::default::Default;
    use std::env;
    use std::path::Path;
    use std::result::Result;

    use self::cloudkms1::CloudKMS;
    use self::cloudkms1::{DecryptRequest, EncryptRequest};
    use self::hyper::net::HttpsConnector;
    use self::hyper::status::StatusCode;
    use self::hyper_rustls::TlsClient;
    use self::oauth2::{ServiceAccountAccess, ServiceAccountKey};

    use crate::kms::{EncryptedDEK, KmsError, KmsProvider, PlaintextDEK, AD};

    const GOOGLE_APP_CREDS: &str = &"GOOGLE_APPLICATION_CREDENTIALS";

    /// Google Cloud Key Management Service
    /// https://cloud.google.com/kms/
    pub struct GcpKms {
        key_resource_id: String,
        service_account: ServiceAccountKey,
    }

    impl GcpKms {
        ///
        /// Create a new GcpKms from a Google Cloud KMS key resource ID of the form
        /// `projects/*/locations/*/keyRings/*/cryptoKeys/*`
        ///
        pub fn from_resource_id(resource_id: &str) -> Result<Self, KmsError> {
            let svc_acct = load_gcp_credential()?;

            Ok(GcpKms {
                key_resource_id: resource_id.to_string(),
                service_account: svc_acct,
            })
        }

        fn new_hub(&self) -> CloudKMS<hyper::Client, ServiceAccountAccess<hyper::Client>> {
            let client1 = hyper::Client::with_connector(HttpsConnector::new(TlsClient::new()));
            let access = oauth2::ServiceAccountAccess::new(self.service_account.clone(), client1);

            let client2 = hyper::Client::with_connector(HttpsConnector::new(TlsClient::new()));
            CloudKMS::new(client2, access)
        }

        fn pretty_http_error(&self, resp: &hyper::client::Response) -> KmsError {
            let code = resp.status;
            let url = &resp.url;

            KmsError::OperationFailed(format!("Response {} from {}", code, url))
        }
    }

    impl KmsProvider for GcpKms {
        fn encrypt_dek(&self, plaintext_dek: &PlaintextDEK) -> Result<EncryptedDEK, KmsError> {
            let mut request = EncryptRequest::default();
            request.plaintext = Some(base64::encode(plaintext_dek));
            request.additional_authenticated_data = Some(base64::encode(AD));

            let hub = self.new_hub();
            let result = hub
                .projects()
                .locations_key_rings_crypto_keys_encrypt(request, &self.key_resource_id)
                .doit();

            match result {
                Ok((http_resp, enc_resp)) => {
                    if http_resp.status == StatusCode::Ok {
                        let ciphertext = enc_resp.ciphertext.unwrap();
                        let ct = base64::decode(&ciphertext)?;
                        Ok(ct)
                    } else {
                        Err(self.pretty_http_error(&http_resp))
                    }
                }
                Err(e) => Err(KmsError::OperationFailed(format!("encrypt_dek() {:?}", e))),
            }
        }

        fn decrypt_dek(&self, encrypted_dek: &EncryptedDEK) -> Result<PlaintextDEK, KmsError> {
            let mut request = DecryptRequest::default();
            request.ciphertext = Some(base64::encode(encrypted_dek));
            request.additional_authenticated_data = Some(base64::encode(AD));

            let hub = self.new_hub();
            let result = hub
                .projects()
                .locations_key_rings_crypto_keys_decrypt(request, &self.key_resource_id)
                .doit();

            match result {
                Ok((http_resp, enc_resp)) => {
                    if http_resp.status == StatusCode::Ok {
                        let plaintext = enc_resp.plaintext.unwrap();
                        let ct = base64::decode(&plaintext)?;
                        Ok(ct)
                    } else {
                        Err(self.pretty_http_error(&http_resp))
                    }
                }
                Err(e) => Err(KmsError::OperationFailed(format!("decrypt_dek() {:?}", e))),
            }
        }
    }

    /// Minimal implementation of Application Default Credentials.
    /// https://cloud.google.com/docs/authentication/production
    ///
    ///   1. Look for GOOGLE_APPLICATION_CREDENTIALS and load service account
    ///      credentials if found.
    ///   2. If not, error
    ///
    /// TODO attempt to load GCE default credentials from metadata server.
    /// This will be a bearer token instead of service account credential.

    fn load_gcp_credential() -> Result<ServiceAccountKey, KmsError> {
        if let Ok(gac) = env::var(GOOGLE_APP_CREDS.to_string()) {
            if Path::new(&gac).exists() {
                match oauth2::service_account_key_from_file(&gac) {
                    Ok(svc_acct_key) => return Ok(svc_acct_key),
                    Err(e) => {
                        return Err(KmsError::InvalidConfiguration(format!(
                            "Can't load service account credential '{}': {:?}",
                            gac, e
                        )))
                    }
                }
            } else {
                return Err(KmsError::InvalidConfiguration(format!(
                    "{} ='{}' does not exist",
                    GOOGLE_APP_CREDS, gac
                )));
            }
        }

        // TODO: call to GCE metadata service to get default credential from
        // http://169.254.169.254/computeMetadata/v1/instance/service-accounts/default/token

        panic!(
            "Failed to load service account credential. Is {} set?",
            GOOGLE_APP_CREDS
        );
    }
}
