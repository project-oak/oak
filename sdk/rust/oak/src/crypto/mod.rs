//
// Copyright 2019 The Project Oak Authors
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

//! Helper library for accessing the Oak cryptography service.

use crate::{grpc, proto::oak::crypto};
use oak_abi::{
    label::Label,
    proto::oak::application::{
        node_configuration::ConfigType, CryptoConfiguration, NodeConfiguration,
    },
};
use prost::Message;
use tink_proto::KeyTemplate;

/// Local representation of the connection to an external crypto service.
pub struct Crypto {
    client: crypto::OakCryptoClient,
}

/// Opaque handle for a keyset, which is a collection of key material held
/// by the Oak crypto pseudo-Node.
pub type KeysetHandle = u64;

/// Format of an encrypted keyset.
pub enum KeysetFormat {
    /// Binary-encoded protobuf.
    Binary,
    /// JSON-encoded protobuf.
    Json,
}

impl Crypto {
    /// Creates a [`Crypto`] instance using the given configuration and label.
    pub fn new(config: &CryptoConfiguration, label: &Label) -> Option<Crypto> {
        let config = NodeConfiguration {
            config_type: Some(ConfigType::CryptoConfig(config.clone())),
        };
        crate::io::node_create("crypto", label, &config)
            .map(|invocation_sender| Crypto {
                client: crypto::OakCryptoClient(invocation_sender),
            })
            .ok()
    }

    /// Generate a new keyset with a single fresh key that matches a specified template.
    pub fn generate(&self, template: KeyTemplate) -> grpc::Result<KeysetHandle> {
        let mut template_data = vec![];
        template.encode(&mut template_data).unwrap();
        let rsp = self.client.generate(crypto::KeysetGenerateRequest {
            template_id: Some(crypto::keyset_generate_request::TemplateId::TemplateData(
                template_data,
            )),
        })?;
        Ok(rsp.keyset_handle)
    }

    /// Generate a new keyset with a single fresh key that matches a template specified by name.
    pub fn generate_named(&self, template_name: &str) -> grpc::Result<KeysetHandle> {
        let rsp = self.client.generate(crypto::KeysetGenerateRequest {
            template_id: Some(crypto::keyset_generate_request::TemplateId::TemplateName(
                template_name.to_string(),
            )),
        })?;
        Ok(rsp.keyset_handle)
    }

    /// Generate a new keyset that just holds public key information
    /// derived from an existing keyset that has private key information.
    pub fn public(&self, kh: KeysetHandle) -> grpc::Result<KeysetHandle> {
        let rsp = self.client.public(crypto::KeysetPublicRequest {
            private_keyset_handle: kh,
        })?;
        Ok(rsp.keyset_handle)
    }

    /// Convert a keyset to an encrypted form using another keyset.
    pub fn bind(
        &self,
        kh: KeysetHandle,
        inner_kh: KeysetHandle,
        format: KeysetFormat,
    ) -> grpc::Result<Vec<u8>> {
        let rsp = self.client.bind(crypto::KeysetBindRequest {
            keyset_handle: kh,
            inner_keyset_handle: inner_kh,
            format: match format {
                KeysetFormat::Binary => crypto::KeysetFormat::Binary as i32,
                KeysetFormat::Json => crypto::KeysetFormat::Json as i32,
            },
        })?;
        Ok(rsp.encrypted_keyset)
    }

    /// Retrieve a keyset from an encrypted form using another keyset.
    pub fn unbind(
        &self,
        kh: KeysetHandle,
        encrypted_keyset: &[u8],
        format: KeysetFormat,
    ) -> grpc::Result<KeysetHandle> {
        let rsp = self.client.unbind(crypto::KeysetUnbindRequest {
            keyset_handle: kh,
            encrypted_keyset: encrypted_keyset.to_vec(),
            format: match format {
                KeysetFormat::Binary => crypto::KeysetFormat::Binary as i32,
                KeysetFormat::Json => crypto::KeysetFormat::Json as i32,
            },
        })?;
        Ok(rsp.keyset_handle)
    }

    /// Return a keyset that acts as a proxy to key material held in
    /// an external KMS.
    pub fn kms_proxy(&self, kms_id: &str) -> grpc::Result<KeysetHandle> {
        let rsp = self.client.kms_proxy(crypto::KmsProxyRequest {
            kms_identifier: kms_id.to_string(),
        })?;
        Ok(rsp.keyset_handle)
    }

    /// AEAD encryption.
    pub fn encrypt(&self, kh: KeysetHandle, pt: &[u8], aad: &[u8]) -> grpc::Result<Vec<u8>> {
        let rsp = self.client.encrypt(crypto::AeadEncryptRequest {
            keyset_handle: kh,
            plaintext: pt.to_vec(),
            associated_data: aad.to_vec(),
        })?;
        Ok(rsp.ciphertext)
    }

    /// AEAD decryption.
    pub fn decrypt(&self, kh: KeysetHandle, ct: &[u8], aad: &[u8]) -> grpc::Result<Vec<u8>> {
        let rsp = self.client.decrypt(crypto::AeadDecryptRequest {
            keyset_handle: kh,
            ciphertext: ct.to_vec(),
            associated_data: aad.to_vec(),
        })?;
        Ok(rsp.plaintext)
    }

    /// Deterministic AEAD encryption.
    pub fn encrypt_deterministically(
        &self,
        kh: KeysetHandle,
        pt: &[u8],
        aad: &[u8],
    ) -> grpc::Result<Vec<u8>> {
        let rsp =
            self.client
                .encrypt_deterministically(crypto::DeterministicAeadEncryptRequest {
                    keyset_handle: kh,
                    plaintext: pt.to_vec(),
                    associated_data: aad.to_vec(),
                })?;
        Ok(rsp.ciphertext)
    }

    /// Deterministic AEAD decryption.
    pub fn decrypt_deterministically(
        &self,
        kh: KeysetHandle,
        ct: &[u8],
        aad: &[u8],
    ) -> grpc::Result<Vec<u8>> {
        let rsp =
            self.client
                .decrypt_deterministically(crypto::DeterministicAeadDecryptRequest {
                    keyset_handle: kh,
                    ciphertext: ct.to_vec(),
                    associated_data: aad.to_vec(),
                })?;
        Ok(rsp.plaintext)
    }

    /// Compute MAC.
    pub fn compute_mac(&self, kh: KeysetHandle, data: &[u8]) -> grpc::Result<Vec<u8>> {
        let rsp = self.client.compute_mac(crypto::ComputeMacRequest {
            keyset_handle: kh,
            data: data.to_vec(),
        })?;
        Ok(rsp.mac_value)
    }

    /// Verify MAC.
    pub fn verify_mac(&self, kh: KeysetHandle, data: &[u8], mac: &[u8]) -> grpc::Result<()> {
        let _rsp = self.client.verify_mac(crypto::VerifyMacRequest {
            keyset_handle: kh,
            data: data.to_vec(),
            mac_value: mac.to_vec(),
        })?;
        Ok(())
    }

    /// Compute PRF.
    pub fn compute_prf(
        &self,
        kh: KeysetHandle,
        data: &[u8],
        output_length: u64,
    ) -> grpc::Result<Vec<u8>> {
        let rsp = self.client.compute_prf(crypto::ComputePrfRequest {
            keyset_handle: kh,
            data: data.to_vec(),
            output_length,
        })?;
        Ok(rsp.prf_value)
    }

    /// Generate signature.
    pub fn sign(&self, kh: KeysetHandle, data: &[u8]) -> grpc::Result<Vec<u8>> {
        let rsp = self.client.sign(crypto::SignatureSignRequest {
            private_keyset_handle: kh,
            data: data.to_vec(),
        })?;
        Ok(rsp.signature)
    }

    /// Verify signature.
    pub fn verify(&self, kh: KeysetHandle, data: &[u8], sig: &[u8]) -> grpc::Result<()> {
        let _rsp = self.client.verify(crypto::SignatureVerifyRequest {
            public_keyset_handle: kh,
            data: data.to_vec(),
            signature: sig.to_vec(),
        })?;
        Ok(())
    }
}
