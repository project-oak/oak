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

use crate::image::{self, Image};
use futures_util::future::FutureExt;
use proto::oak::containers::{image_loader_server::ImageLoader, LoadRequest};
use std::net::SocketAddr;
use tokio::sync::{mpsc::Sender, oneshot::Receiver};
use tonic::{transport::Server, Code, Request, Response, Result, Status, Streaming};

pub mod proto {
    pub mod oak {
        pub mod containers {
            tonic::include_proto!("oak.containers");
        }
    }
}

pub struct ImageLoaderServer {
    loaded_tx: Sender<Image>,
}

#[tonic::async_trait]
impl ImageLoader for ImageLoaderServer {
    async fn load(&self, request: Request<Streaming<LoadRequest>>) -> Result<Response<()>> {
        let mut stream = request.into_inner();

        // We should see if this could be streamed, somehow, instead of buffering the whole file in
        // memory before unpacking it.
        let mut buf = Vec::new();
        while let Some(mut msg) = stream.message().await? {
            buf.append(&mut msg.image_chunk);
        }
        let image = Image::new(String::from(image::RAMFS_TMP_DIR))?;
        image.unpack(&buf)?;
        // this is now ready to launch, but don't do it here, otherwise we will never be able to
        // send a response back as it'd terminate stage1
        self.loaded_tx
            .send(image)
            .await
            .map_err(|err| Status::new(Code::Internal, err.to_string()))?;
        Ok(Response::new(()))
    }
}

impl ImageLoaderServer {
    pub async fn serve(
        addr: SocketAddr,
        shutdown: Receiver<()>,
        loaded_tx: Sender<Image>,
    ) -> Result<(), tonic::transport::Error> {
        let server = ImageLoaderServer { loaded_tx };

        Server::builder()
            .add_service(
                proto::oak::containers::image_loader_server::ImageLoaderServer::new(server),
            )
            .serve_with_shutdown(addr, shutdown.map(drop))
            .await
    }
}
