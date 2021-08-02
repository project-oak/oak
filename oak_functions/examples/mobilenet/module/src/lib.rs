//
// Copyright 2021 The Project Oak Authors
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

//! Oak Functions TensorFlow example, based on the MobilenetV2 example
//! in https://github.com/sonos/tract/tree/main/examples/tensorflow-mobilenet-v2.

#![feature(try_blocks)]

use oak_functions_abi::proto::Inference;

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    let response = match handle_request() {
        Ok(inference) => {
            let best = inference
                .inference_vec
                .iter()
                .cloned()
                .zip(1..)
                .max_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
            format!("Best result: {:?}", best)
        }
        Err(e) => format!("Could not get image category: {:?}", e),
    };

    // Write the response.
    oak_functions::write_response(response.as_bytes()).expect("Couldn't write the response body.");
}

/// Reads the request containing an image, gets the inference from the TensorFlow model using Oak
/// Functions ABI, and returns the resulting inference vector.
fn handle_request() -> anyhow::Result<Inference> {
    // Get the image from the request
    let request_bytes = oak_functions::read_request()
        .map_err(|err| anyhow::anyhow!("could not read request body: {:?}", err))?;

    // Get image category
    oak_functions::tf_model_infer(&request_bytes)
        .map_err(|err| anyhow::anyhow!("could not get inference: {:?}", err))
}
