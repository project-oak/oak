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

#![no_std]
#![no_main]
#![feature(alloc_error_handler)]
#![feature(never_type)]

extern crate alloc;

use alloc::{boxed::Box, format};

use oak_restricted_kernel_sdk::{
    attestation::InstanceAttester,
    channel::{start_blocking_server, FileDescriptorChannel},
    crypto::InstanceSigner,
    entrypoint,
    utils::samplestore::StaticSampleStore,
    Attester, Signer,
};
use rand_core::{CryptoRng, OsRng, RngCore};
use service::oak;
use sha2::{Digest, Sha256};

#[entrypoint]
fn start_server() -> ! {
    let mut invocation_stats = StaticSampleStore::<1000>::new().unwrap();
    let attester = InstanceAttester::create().expect("couldn't create attester");
    let signer = InstanceSigner::create().expect("couldn't create signer");
    let service = FlagDigestService { attester, signer };
    let server = oak::ctf_sha2::enclave::FlagDigestServiceServer::new(service);
    start_blocking_server(Box::<FileDescriptorChannel>::default(), server, &mut invocation_stats)
        .expect("server encountered an unrecoverable error");
}

struct FlagDigestService<A: Attester, B: Signer> {
    attester: A,
    signer: B,
}

impl<A, B> oak::ctf_sha2::enclave::FlagDigestService for FlagDigestService<A, B>
where
    A: Attester,
    B: Signer,
{
    fn generate_flag_digest(
        &mut self,
        _request: oak::ctf_sha2::enclave::GenerateFlagDigestRequest,
    ) -> Result<oak::ctf_sha2::enclave::GenerateFlagDigestResponse, micro_rpc::Status> {
        // Initialize an empty byte array which will be filled with the secret flag.
        let mut flag = [0; 64];

        // We must use a cryptographically secure RNG.
        // See <https://rust-random.github.io/book/guide-gen.html#cryptographically-secure-pseudo-random-number-generator>.
        let mut rng = OsRng;
        // Assert the RNG implements the required marker trait, to make sure it is not
        // accidentally replaced with a non-cryptographically secure RNG.
        assert_crypto_rng(&rng);
        rng.fill_bytes(&mut flag);

        let mut hasher = Sha256::new();
        hasher.update(flag);
        let flag_digest = hasher.finalize().to_vec();

        // Sign the flag digest using this enclave application's signing key.
        let signature = self.signer.sign(flag_digest.as_slice());

        // Fetch Restricted Kernel evidence.
        let evidence = self.attester.quote().map_err(|err| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::Internal,
                format!("failed to get evidence: {err}"),
            )
        })?;

        Ok(oak::ctf_sha2::enclave::GenerateFlagDigestResponse {
            flag_digest,
            signature,
            evidence: Some(evidence),
        })
    }
}

fn assert_crypto_rng<T: CryptoRng>(_rng: &T) {}
