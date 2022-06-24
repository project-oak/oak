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

//! Sends an image to the mobilenet application and checks that the response is correct.

use anyhow::Context;
use oak_functions_abi::Request;
use oak_functions_client::Client;
use regex::Regex;
use tract_tensorflow::prelude::*;

// Shape of the input tensor
const BATCH_SIZE: usize = 1;
const WIDTH: u32 = 224;
const HEIGHT: u32 = 224;
const CHANNELS: usize = 3;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let mut client = Client::new("http://localhost:8080")
        .await
        .context("Could not create Oak Functions client")?;

    let image_buffer = image::open("oak_functions/examples/mobilenet/files/oak.jpg")
        .unwrap()
        .to_rgb8();

    // Resize the image
    let resized = image::imageops::resize(
        &image_buffer,
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

    let request = Request {
        body: bytes.to_vec(),
    };

    let response = client
        .invoke(request)
        .await
        .context("Could not invoke Oak Functions")?;

    // Allow some small variance in the result, as the number can change slightly between different
    // versions of libraries. We still want the test to fail for any significant changes, though.
    let response_body = std::str::from_utf8(response.body().unwrap()).unwrap();
    let regex = Regex::new(r"^Best result: Some\(\(0.175232\d+, 789\)\)$").unwrap();
    assert!(
        regex.is_match(response_body),
        "Response \"{}\" does not match regex \"{}\"",
        response_body,
        regex.as_str()
    );

    Ok(())
}
