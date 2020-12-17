//
// Copyright 2020 The Project Oak Authors
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

use super::rpc_status;
use oak_services::proto::{
    google::{rpc, rpc::Code},
    oak::{crypto, crypto::keyset_generate_request::TemplateId},
};
use prost::Message;
use rand::RngCore;
use std::collections::HashMap;

/// Helper to convert a [`tink_core::TinkError`] to an [`rpc::Status`].
fn tinkerr(e: tink_core::TinkError) -> rpc::Status {
    rpc_status(Code::Internal, format!("{:?}", e))
}

/// Wrapper around the Tink cryptographic library which maintains a map
/// from opaque `u64` values to `[tink_core::keyset::Handle`] objects.
pub struct TinkWrapper {
    handles: HashMap<u64, tink_core::keyset::Handle>,
}

impl TinkWrapper {
    pub fn new() -> TinkWrapper {
        tink_aead::init();
        tink_daead::init();
        tink_mac::init();
        tink_prf::init();
        tink_signature::init();
        TinkWrapper {
            handles: HashMap::new(),
        }
    }

    /// Register a [`tink_core::keyset::Handle`] and return an opaque `u64` that will
    /// be used to refer to this keyset on the gRPC API.
    fn register_handle(&mut self, kh: tink_core::keyset::Handle) -> u64 {
        loop {
            let candidate = rand::thread_rng().next_u64();
            if self.handles.get(&candidate).is_none() {
                self.handles.insert(candidate, kh);
                return candidate;
            }
        }
    }

    /// Retrieve the [`tink_core::keyset::Handle`] that corresponds to an opaque `u64` value.
    fn get_handle(&self, h: u64) -> Result<&tink_core::keyset::Handle, rpc::Status> {
        self.handles
            .get(&h)
            .ok_or_else(|| rpc_status(Code::InvalidArgument, "unknown keyset handle".to_string()))
    }

    pub fn generate(
        &mut self,
        req: crypto::KeysetGenerateRequest,
    ) -> Result<crypto::KeysetResponse, rpc::Status> {
        let template_id = req
            .template_id
            .ok_or_else(|| rpc_status(Code::InvalidArgument, "missing template ID".to_string()))?;
        let key_template = match template_id {
            TemplateId::TemplateData(data) => {
                tink_proto::KeyTemplate::decode(&*data).map_err(|e| {
                    rpc_status(
                        Code::InvalidArgument,
                        format!("failed to decode template: {:?}", e),
                    )
                })?
            }
            TemplateId::TemplateName(name) => {
                let generator =
                    tink_core::registry::get_template_generator(&name).ok_or_else(|| {
                        rpc_status(
                            Code::InvalidArgument,
                            format!("unknown template name {}", name),
                        )
                    })?;
                generator()
            }
        };
        let kh = tink_core::keyset::Handle::new(&key_template).unwrap();
        let api_handle = self.register_handle(kh);
        Ok(crypto::KeysetResponse {
            keyset_handle: api_handle,
        })
    }

    pub fn public(
        &mut self,
        req: crypto::KeysetPublicRequest,
    ) -> Result<crypto::KeysetResponse, rpc::Status> {
        let priv_kh = self.get_handle(req.private_keyset_handle)?;
        let pub_kh = priv_kh.public().map_err(tinkerr)?;
        let api_handle = self.register_handle(pub_kh);
        Ok(crypto::KeysetResponse {
            keyset_handle: api_handle,
        })
    }

    pub fn bind(
        &self,
        req: crypto::KeysetBindRequest,
    ) -> Result<crypto::KeysetBindResponse, rpc::Status> {
        let kh = self.get_handle(req.keyset_handle)?;
        let aead = tink_aead::new(&kh).map_err(tinkerr)?;
        let inner_kh = self.get_handle(req.inner_keyset_handle)?;

        let mut encrypted_keyset = vec![];
        match crypto::KeysetFormat::from_i32(req.format) {
            Some(crypto::KeysetFormat::Binary) => write_keyset_with(
                tink_core::keyset::BinaryWriter::new(&mut encrypted_keyset),
                aead,
                inner_kh,
            )?,
            Some(crypto::KeysetFormat::Json) => write_keyset_with(
                tink_core::keyset::JsonWriter::new(&mut encrypted_keyset),
                aead,
                inner_kh,
            )?,
            _ => {
                return Err(rpc_status(
                    Code::InvalidArgument,
                    "invalid keyset format".to_string(),
                ))
            }
        }

        Ok(crypto::KeysetBindResponse { encrypted_keyset })
    }

    pub fn unbind(
        &mut self,
        req: crypto::KeysetUnbindRequest,
    ) -> Result<crypto::KeysetResponse, rpc::Status> {
        let kh = self.get_handle(req.keyset_handle)?;
        let aead = tink_aead::new(&kh).map_err(tinkerr)?;

        let inner_kh = match crypto::KeysetFormat::from_i32(req.format) {
            Some(crypto::KeysetFormat::Binary) => read_keyset_with(
                tink_core::keyset::BinaryReader::new(std::io::Cursor::new(req.encrypted_keyset)),
                aead,
            )?,
            Some(crypto::KeysetFormat::Json) => read_keyset_with(
                tink_core::keyset::JsonReader::new(std::io::Cursor::new(req.encrypted_keyset)),
                aead,
            )?,
            _ => {
                return Err(rpc_status(
                    Code::InvalidArgument,
                    "invalid keyset format".to_string(),
                ))
            }
        };

        let api_handle = self.register_handle(inner_kh);
        Ok(crypto::KeysetResponse {
            keyset_handle: api_handle,
        })
    }

    pub fn kms_proxy(
        &self,
        _req: crypto::KmsProxyRequest,
    ) -> Result<crypto::KeysetResponse, rpc::Status> {
        // TODO(#745): implement KMS integration
        Err(rpc_status(Code::Internal, "not implemented".to_string()))
    }

    pub fn encrypt(
        &self,
        req: crypto::AeadEncryptRequest,
    ) -> Result<crypto::AeadEncryptResponse, rpc::Status> {
        let kh = self.get_handle(req.keyset_handle)?;
        let d = tink_aead::new(&kh).map_err(tinkerr)?;
        let ct = d
            .encrypt(&req.plaintext, &req.associated_data)
            .map_err(tinkerr)?;
        Ok(crypto::AeadEncryptResponse { ciphertext: ct })
    }

    pub fn decrypt(
        &self,
        req: crypto::AeadDecryptRequest,
    ) -> Result<crypto::AeadDecryptResponse, rpc::Status> {
        let kh = self.get_handle(req.keyset_handle)?;
        let d = tink_aead::new(&kh).map_err(tinkerr)?;
        let pt = d
            .decrypt(&req.ciphertext, &req.associated_data)
            .map_err(tinkerr)?;
        Ok(crypto::AeadDecryptResponse { plaintext: pt })
    }

    pub fn encrypt_deterministically(
        &self,
        req: crypto::DeterministicAeadEncryptRequest,
    ) -> Result<crypto::DeterministicAeadEncryptResponse, rpc::Status> {
        let kh = self.get_handle(req.keyset_handle)?;
        let d = tink_daead::new(&kh).map_err(tinkerr)?;
        let ct = d
            .encrypt_deterministically(&req.plaintext, &req.associated_data)
            .map_err(tinkerr)?;
        Ok(crypto::DeterministicAeadEncryptResponse { ciphertext: ct })
    }

    pub fn decrypt_deterministically(
        &self,
        req: crypto::DeterministicAeadDecryptRequest,
    ) -> Result<crypto::DeterministicAeadDecryptResponse, rpc::Status> {
        let kh = self.get_handle(req.keyset_handle)?;
        let d = tink_daead::new(&kh).map_err(tinkerr)?;
        let pt = d
            .decrypt_deterministically(&req.ciphertext, &req.associated_data)
            .map_err(tinkerr)?;
        Ok(crypto::DeterministicAeadDecryptResponse { plaintext: pt })
    }

    pub fn compute_mac(
        &self,
        req: crypto::ComputeMacRequest,
    ) -> Result<crypto::ComputeMacResponse, rpc::Status> {
        let kh = self.get_handle(req.keyset_handle)?;
        let d = tink_mac::new(&kh).map_err(tinkerr)?;
        let mac = d.compute_mac(&req.data).map_err(tinkerr)?;
        Ok(crypto::ComputeMacResponse { mac_value: mac })
    }

    pub fn verify_mac(
        &self,
        req: crypto::VerifyMacRequest,
    ) -> Result<crypto::VerifyMacResponse, rpc::Status> {
        let kh = self.get_handle(req.keyset_handle)?;
        let d = tink_mac::new(&kh).map_err(tinkerr)?;
        d.verify_mac(&req.mac_value, &req.data).map_err(tinkerr)?;
        Ok(crypto::VerifyMacResponse {})
    }

    pub fn compute_prf(
        &self,
        req: crypto::ComputePrfRequest,
    ) -> Result<crypto::ComputePrfResponse, rpc::Status> {
        let kh = self.get_handle(req.keyset_handle)?;
        let d = tink_prf::Set::new(&kh).map_err(tinkerr)?;
        let prf = d
            .compute_primary_prf(&req.data, req.output_length as usize)
            .map_err(tinkerr)?;
        Ok(crypto::ComputePrfResponse { prf_value: prf })
    }

    pub fn sign(
        &self,
        req: crypto::SignatureSignRequest,
    ) -> Result<crypto::SignatureSignResponse, rpc::Status> {
        let kh = self.get_handle(req.private_keyset_handle)?;
        let d = tink_signature::new_signer(&kh).map_err(tinkerr)?;
        let sig = d.sign(&req.data).map_err(tinkerr)?;
        Ok(crypto::SignatureSignResponse { signature: sig })
    }

    pub fn verify(
        &self,
        req: crypto::SignatureVerifyRequest,
    ) -> Result<crypto::SignatureVerifyResponse, rpc::Status> {
        let kh = self.get_handle(req.public_keyset_handle)?;
        let d = tink_signature::new_verifier(&kh).map_err(tinkerr)?;
        d.verify(&req.signature, &req.data).map_err(tinkerr)?;
        Ok(crypto::SignatureVerifyResponse {})
    }
}

fn write_keyset_with<T: tink_core::keyset::Writer>(
    mut writer: T,
    aead: Box<dyn tink_core::Aead>,
    inner_kh: &tink_core::keyset::Handle,
) -> Result<(), rpc::Status> {
    inner_kh.write(&mut writer, aead).map_err(tinkerr)
}

fn read_keyset_with<T: tink_core::keyset::Reader>(
    mut reader: T,
    aead: Box<dyn tink_core::Aead>,
) -> Result<tink_core::keyset::Handle, rpc::Status> {
    tink_core::keyset::Handle::read(&mut reader, aead).map_err(tinkerr)
}
