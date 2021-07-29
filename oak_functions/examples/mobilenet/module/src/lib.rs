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

mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.mobilenet.rs"));
}

use oak_functions_abi::proto::Inference;
use prost::Message;
use tract_tensorflow::prelude::*;

// Shape of the input tensor
const BATCH_SIZE: usize = 1;
const WIDTH: u32 = 224;
const HEIGHT: u32 = 224;
const CHANNELS: usize = 3;

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

/// Reads the request containing an image. Reshapes and converts the image into the format expected
/// by the MobilenetV2 model. Gets the inference from the TensorFlow model using Oak Functions ABI,
/// and returns the resulting inference vector.
fn handle_request() -> anyhow::Result<Inference> {
    // Get the image from the request
    let request_bytes = oak_functions::read_request().expect("could not read request body");
    let image =
        proto::MobilenetImage::decode(&*request_bytes).expect("could not decode MobilenetImage");

    // Resize the image
    let recreated_image = image::RgbImage::from_raw(image.width, image.height, image.image)
        .ok_or_else(|| anyhow::anyhow!("could not recreate image"))?;
    let resized = image::imageops::resize(
        &recreated_image,
        WIDTH,
        HEIGHT,
        ::image::imageops::FilterType::Triangle,
    );

    // Convert to tensor
    let tensor: Tensor = tract_ndarray::Array4::from_shape_fn(
        (BATCH_SIZE, WIDTH as usize, HEIGHT as usize, CHANNELS),
        |(_, y, x, c)| resized[(x as _, y as _)][c] as f32 / 255.0,
    )
    .into();
    let bytes = unsafe { tensor.as_bytes() };

    // Get image category
    let inference = oak_functions::tf_model_infer(bytes).expect("could not get inference");
    Ok(inference)
}
