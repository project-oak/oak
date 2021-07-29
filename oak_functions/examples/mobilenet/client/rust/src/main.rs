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

mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.mobilenet.rs"));
}

use anyhow::Context;
use oak_functions_abi::proto::Request;
use oak_functions_client::Client;
use prost::Message;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();

    let mut client = Client::new("http://localhost:8080")
        .await
        .context("Could not create Oak Functions client")?;

    let image_buffer = image::open("oak_functions/examples/mobilenet/oak.jpg")
        .unwrap()
        .to_rgb8();

    let image = proto::MobilenetImage {
        width: image_buffer.width(),
        height: image_buffer.height(),
        image: image_buffer.to_vec(),
    };

    let mut encoded_image = Vec::new();
    image
        .encode(&mut encoded_image)
        .context("Error encoding the image")?;

    let request = Request {
        body: encoded_image,
    };

    let response = client
        .invoke(request)
        .await
        .context("Could not invoke Oak Functions")?;

    let response_body = std::str::from_utf8(response.body().unwrap()).unwrap();
    assert_eq!(response_body, "Best result: Some((0.17839512, 789))");

    Ok(())
}
