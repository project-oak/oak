//
// Copyright 2020 The Project Oak Authors
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

use futures::stream::StreamExt;
use log::{error, info};
use tokio::{
    io,
    net::{TcpListener, TcpStream},
    spawn,
};

#[tokio::main]
async fn main() -> io::Result<()> {
    env_logger::init();
    let in_address = "[::1]:50051";
    let listener = TcpListener::bind(in_address).await?;
    info!("Proxy listening on {:?}", in_address);
    proxy(listener).await?;
    Ok(())
}

async fn proxy(mut listener: TcpListener) -> io::Result<()> {
    let mut incoming = listener.incoming();
    while let Some(connection_in) = incoming.next().await {
        match connection_in {
            Err(e) => error!("Accept incoming failed: {:?}", e),
            Ok(stream_in) => {
                info!("Accepted incoming connection.");
                spawn(handle_connection(stream_in)).await??;
            }
        }
    }
    Ok(())
}

async fn handle_connection(stream_in: TcpStream) -> io::Result<()> {
    let out_address = "[::1]:50052";
    info!("Attempting to connect to {:?}", out_address);
    let connection_out = TcpStream::connect(out_address).await;
    match connection_out {
        Err(e) => error!("Connect to {:?} failed: {:?}", out_address, e),
        Ok(stream_out) => {
            info!("Connected to {:?}", out_address);
            let (mut reader_up, mut writer_down) = io::split(stream_in);
            let (mut reader_down, mut writer_up) = io::split(stream_out);

            let up = spawn(async move { io::copy(&mut reader_up, &mut writer_up).await });
            let down = spawn(async move { io::copy(&mut reader_down, &mut writer_down).await });

            match up.await? {
                Err(e) => error!("Error copying to server: {:?}", e),
                Ok(count) => info!("Copied {:?} bytes to server", count),
            }
            match down.await? {
                Err(e) => error!("Error copying to client: {:?}", e),
                Ok(count) => info!("Copied {:?} bytes to client", count),
            }
        }
    }
    Ok(())
}
