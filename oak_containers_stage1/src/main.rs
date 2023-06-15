//
// Copyright 2023 The Project Oak Authors
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

#![feature(never_type)]

mod image;

use crate::proto::oak::containers::launcher_client::LauncherClient;
use clap::Parser;
use image::Image;
use std::error::Error;
use tonic::transport::{Channel, Uri};

mod proto {
    pub mod oak {
        pub mod containers {
            tonic::include_proto!("oak.containers");
        }
    }
}

#[derive(Parser, Debug)]
struct Args {
    #[arg(required = true)]
    addr: Uri,

    #[arg(default_value = "/sbin/init")]
    init: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    let channel = Channel::builder(args.addr).connect().await?;
    let mut client = LauncherClient::new(channel);
    let image = Image::new(String::from(image::RAMFS_TMP_DIR))?;

    // We should see if this could be streamed, somehow, instead of buffering the whole file in
    // memory before unpacking it.
    let mut buf = Vec::new();
    {
        let request = client.get_oak_system_image(tonic::Request::new(())).await?;
        let mut stream = request.into_inner();

        while let Some(mut msg) = stream.message().await? {
            buf.append(&mut msg.image_chunk);
        }
    }

    image.unpack(&buf)?;
    image.switch(&args.init)?
}
