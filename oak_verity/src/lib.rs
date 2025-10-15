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

//! Oak Verity - A service for executing Wasm modules and producing verifiable
//! manifests
//!
//! This library provides the core functionality for Oak Verity, which executes
//! WebAssembly modules using the same ABI as Oak Functions and produces
//! manifests containing digests of inputs and outputs for verification
//! purposes.

use std::collections::BTreeMap;

use anyhow::{Context, Result};
use oak_attestation_types::assertion_generator::AssertionGenerator;
use oak_functions_service::{
    instance::OakFunctionsInstance,
    wasm::{WasmConfig, WasmHandler},
};
use oak_proto_rust::oak::{
    functions::InitializeRequest,
    verity::{ExecuteRequest, ExecuteResponse, ExecutionManifest},
    RawDigest,
};
use prost::Message;
use sha2::{Digest, Sha256};

/// Main entry point for Oak Verity execution.
pub struct OakVerity {
    pub assertion_generators: BTreeMap<String, Box<dyn AssertionGenerator>>,
}

impl OakVerity {
    /// Create a new Oak Verity instance.
    pub fn new() -> Result<Self> {
        Ok(Self { assertion_generators: BTreeMap::new() })
    }

    /// Execute a Wasm module with the given request and return the response
    /// with manifest.
    pub fn execute(&self, request: ExecuteRequest) -> Result<ExecuteResponse> {
        // Execute the Wasm module using Oak Functions infrastructure.
        let output_data = self.execute_wasm(&request.wasm_module, &request.input_data)?;

        // Generate the manifest with digests of input, Wasm module, and output.
        let input_digest = Self::create_raw_digest(&request.input_data);
        let wasm_digest = Self::create_raw_digest(&request.wasm_module);
        let output_digest = Self::create_raw_digest(&output_data);

        let manifest = ExecutionManifest {
            input_data_digest: Some(input_digest),
            wasm_module_digest: Some(wasm_digest),
            output_data_digest: Some(output_digest),
        };

        let serialized_manifest = manifest.encode_to_vec();

        let mut assertions = BTreeMap::new();
        for (id, generator) in &self.assertion_generators {
            let assertion = generator.generate(&serialized_manifest)?;
            assertions.insert(id.clone(), assertion);
        }

        Ok(ExecuteResponse { serialized_manifest, assertions, output_data })
    }

    /// Execute a Wasm module with the given input data.
    fn execute_wasm(&self, wasm_module: &[u8], input_data: &[u8]) -> Result<Vec<u8>> {
        // Create an OakFunctionsInstance using the same infrastructure as Oak
        // Functions.
        let initialize_request =
            InitializeRequest { wasm_module: wasm_module.to_vec(), constant_response_size: 0 };

        let instance = OakFunctionsInstance::<WasmHandler>::new(
            &initialize_request,
            None, // No observer for now.
            WasmConfig::default(),
        )
        .context("Failed to create Oak Functions instance")?;

        // Execute the Wasm module with the input data.
        let response_bytes = instance
            .handle_user_request(input_data.to_vec())
            .context("Failed to execute Wasm module")?;

        Ok(response_bytes)
    }

    /// Create a RawDigest with SHA-256 hash.
    fn create_raw_digest(data: &[u8]) -> RawDigest {
        let sha256_hash = compute_sha256_digest(data);
        RawDigest { sha2_256: sha256_hash, ..Default::default() }
    }
}

impl Default for OakVerity {
    fn default() -> Self {
        Self::new().expect("Failed to create OakVerity instance")
    }
}

/// Compute SHA-256 digest of the given data.
pub fn compute_sha256_digest(data: &[u8]) -> Vec<u8> {
    Sha256::digest(data).to_vec()
}

#[cfg(test)]
mod tests {
    use oak_proto_rust::oak::attestation::v1::Assertion;

    use super::*;

    #[test]
    fn test_oak_verity_creation() {
        let oak_verity = OakVerity::new().unwrap();
        assert!(oak_verity.assertion_generators.is_empty());
    }

    #[test]
    fn test_compute_sha256_digest() {
        let test_data = b"hello world";
        let digest = compute_sha256_digest(test_data);

        // SHA-256 should produce 32 bytes.
        assert_eq!(digest.len(), 32);

        // Should be deterministic.
        let digest2 = compute_sha256_digest(test_data);
        assert_eq!(digest, digest2);

        // Different inputs should produce different digests.
        let different_data = b"hello world!";
        let different_digest = compute_sha256_digest(different_data);
        assert_ne!(digest, different_digest);
    }

    #[test]
    fn test_execute_with_assertions() {
        use oak_attestation_types::assertion_generator::AssertionGeneratorError;

        const MOCK_ASSERTION_ID: &str = "z11762005613252036790";

        /// A Mock Assertion Generator that always returns a fixed value for the
        /// assertion, regardless of the data that is passed in.
        struct MockAssertionGenerator;
        impl AssertionGenerator for MockAssertionGenerator {
            fn generate(&self, _data: &[u8]) -> Result<Assertion, AssertionGeneratorError> {
                Ok(Assertion { content: "ok".to_string().into_bytes() })
            }
        }

        let mut oak_verity = OakVerity::new().unwrap();
        oak_verity
            .assertion_generators
            .insert(MOCK_ASSERTION_ID.to_string(), Box::new(MockAssertionGenerator));

        let wasm_module = std::fs::read("oak_functions/examples/echo/echo.wasm").unwrap();

        let request = ExecuteRequest { input_data: b"test input".to_vec(), wasm_module };

        let response = oak_verity.execute(request).unwrap();

        assert!(!response.serialized_manifest.is_empty());
        assert_eq!(response.assertions.len(), 1);
        let assertion = response.assertions.get(MOCK_ASSERTION_ID).unwrap();
        assert_eq!(assertion.content, "ok".to_string().into_bytes());
    }

    // Note: Full integration tests with actual Wasm modules would require
    // compiled Oak Functions-compatible Wasm modules and are better suited
    // for integration test files, contained in the tests folder.
}
