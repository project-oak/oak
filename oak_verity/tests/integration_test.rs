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

//! Integration tests for Oak Verity using real Wasm modules.

use anyhow::Result;
use oak_proto_rust::oak::verity::ExecuteRequest;
use oak_verity::OakVerity;

/// Test Oak Verity with the echo Wasm module.
#[test]
fn test_oak_verity_with_echo_wasm() -> Result<()> {
    // Load the echo Wasm module that's built as part of Oak Functions examples.
    let wasm_module_path = "oak_functions/examples/echo/echo.wasm";
    let wasm_module =
        std::fs::read(wasm_module_path).expect("Failed to read echo.wasm - make sure it's built");

    // Create Oak Verity instance.
    let oak_verity = OakVerity::new()?;

    // Test data.
    let test_input = b"Hello, Oak Verity!";

    // Create execute request.
    let request = ExecuteRequest { input_data: test_input.to_vec(), wasm_module };

    // Execute the Wasm module.
    let response = oak_verity.execute(request)?;

    // Verify the response.
    assert!(!response.output_data.is_empty(), "Output data must not be empty");

    // For echo module, output must match input.
    assert_eq!(
        response.output_data, test_input,
        "Echo module must return the same data that was input"
    );

    // Verify manifest was generated.
    let manifest = response.manifest.expect("Manifest must be present");

    // Verify all digests are present.
    assert!(manifest.input_data_digest.is_some(), "Input data digest must be present");
    assert!(manifest.wasm_module_digest.is_some(), "Wasm module digest must be present");
    assert!(manifest.output_data_digest.is_some(), "Output data digest must be present");

    // Verify digest formats (SHA-256 must be 32 bytes).
    let input_digest = manifest.input_data_digest.unwrap();
    let wasm_digest = manifest.wasm_module_digest.unwrap();
    let output_digest = manifest.output_data_digest.unwrap();

    assert_eq!(input_digest.sha2_256.len(), 32, "Input digest must be 32 bytes (SHA-256)");
    assert_eq!(wasm_digest.sha2_256.len(), 32, "Wasm digest must be 32 bytes (SHA-256)");
    assert_eq!(output_digest.sha2_256.len(), 32, "Output digest must be 32 bytes (SHA-256)");

    // For echo module, input and output must have same digest.
    assert_eq!(
        input_digest.sha2_256, output_digest.sha2_256,
        "Input and output digests must be identical for echo module"
    );

    // Input and Wasm digests must be different.
    assert_ne!(
        input_digest.sha2_256, wasm_digest.sha2_256,
        "Input and Wasm module must have different digests"
    );

    Ok(())
}

/// Test Oak Verity with different input sizes
#[test]
fn test_oak_verity_echo_different_inputs() -> Result<()> {
    let wasm_module_path = "oak_functions/examples/echo/echo.wasm";
    let wasm_module =
        std::fs::read(wasm_module_path).expect("Failed to read echo.wasm - make sure it's built");

    let oak_verity = OakVerity::new()?;

    // Test with different input sizes and content
    let test_cases = [
        b"".to_vec(),      // Empty input
        b"a".to_vec(),     // Single byte
        b"short".to_vec(), // Short string
        b"This is a longer test input with more content to verify Oak Verity works correctly"
            .to_vec(),
        (0..1000).map(|i| (i % 256) as u8).collect(), // Binary data
    ];

    for (i, test_input) in test_cases.iter().enumerate() {
        let request =
            ExecuteRequest { input_data: test_input.clone(), wasm_module: wasm_module.clone() };

        let response =
            oak_verity.execute(request).unwrap_or_else(|_| panic!("Test case {i} must succeed"));

        // Verify echo behavior
        assert_eq!(
            response.output_data, *test_input,
            "Test case {}: Echo must return identical data",
            i
        );

        // Verify manifest
        let manifest =
            response.manifest.unwrap_or_else(|| panic!("Test case {i}: Manifest must exist"));
        let input_digest = manifest
            .input_data_digest
            .unwrap_or_else(|| panic!("Test case {i}: Input digest must exist"));
        let output_digest = manifest
            .output_data_digest
            .unwrap_or_else(|| panic!("Test case {i}: Output digest must exist"));

        assert_eq!(
            input_digest.sha2_256, output_digest.sha2_256,
            "Test case {}: Input and output digests must match for echo",
            i
        );
    }

    Ok(())
}
