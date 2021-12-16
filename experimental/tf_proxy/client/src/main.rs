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

//! Sends a series of TensorFlow Prediction Requests via the proxy and checks the response against
//! the expected labels. Inspired by
//! https://github.com/tensorflow/serving/blob/f3fbec59798e13cb1f7230fcf891c0ec4113331e/tensorflow_serving/example/mnist_client.py

use anyhow::Context;
use log::{debug, info, trace};
use maplit::hashmap;
use oak_functions_abi::proto::{ConfigurationInfo, Request};
use oak_functions_client::Client;
use prost::Message;
use proto::serving::{ModelSpec, PredictRequest, PredictResponse};
use structopt::StructOpt;

mod data;
mod proto {
    // Suppress warning: `all variants have the same prefix: `Dt``.
    #![allow(clippy::enum_variant_names)]
    tonic::include_proto!("tensorflow");
    pub mod serving {
        tonic::include_proto!("tensorflow.serving");
    }
}

#[derive(StructOpt, Clone)]
#[structopt(about = "Oak Functions Client")]
pub struct Opt {
    #[structopt(
        long,
        help = "URI of the Tensorflow Proxy to connect to",
        default_value = "http://localhost:8080"
    )]
    uri: String,
    #[structopt(
        long,
        help = "The working directory for downloading and processing test data",
        default_value = "/tmp"
    )]
    work_dir: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    // Config is not relevant for the proxy for now.
    let config_verifier = |_: ConfigurationInfo| Ok(());

    let mut client = Client::new(&opt.uri, config_verifier)
        .await
        .context("couldn't create client")?;

    let mut error_count = 0;
    let mut count = 0;
    for item in data::get_test_data(&opt.work_dir).await?.iter().take(100) {
        let predict_request = PredictRequest {
            inputs: hashmap! { "images".to_owned() => item.image.clone() },
            model_spec: Some(ModelSpec {
                name: "mnist".to_owned(),
                signature_name: "predict_images".to_owned(),
                version_choice: None,
            }),
            output_filter: Vec::new(),
        };
        trace!("predict request: {:?}", predict_request);

        let request = Request {
            body: predict_request.encode_to_vec(),
        };

        let response = client
            .invoke(request)
            .await
            .context("couldn't invoke Tensorflow Proxy")?;

        let response_body = response.body().unwrap();
        trace!("response body: {:?}", response_body);
        let predict_response =
            PredictResponse::decode(&*response_body).context("couldn't parse response")?;
        trace!("predict response: {:?}", predict_response);

        let scores = predict_response
            .outputs
            .get("scores")
            .ok_or_else(|| anyhow::anyhow!("no scores returned in result"))?;
        let label =
            arg_max(&scores.float_val).ok_or_else(|| anyhow::anyhow!("scores vector is empty"))?;
        debug!("predicted label:{}", label);

        count += 1;
        if label != item.label as usize {
            info!(
                "wrong prediction - expected label: {}, predicted label:{}",
                item.label, label
            );
            error_count += 1;
        }
    }

    if count > 0 {
        println!("Processed {} tests.", count);
        // We expect an error rate around 10%.
        println!(
            "Error rate: {}%",
            100. * (error_count as f32) / (count as f32)
        );
    }

    Ok(())
}

fn arg_max(data: &[f32]) -> Option<usize> {
    data.iter()
        .enumerate()
        .reduce(|(max_index, max_value), (index, value)| {
            if value > max_value {
                (index, value)
            } else {
                (max_index, max_value)
            }
        })
        .map(|(max_index, _)| max_index)
}
