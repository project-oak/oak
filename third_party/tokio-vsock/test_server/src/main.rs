/*
 * Copyright 2019 fsyncd, Berlin, Germany.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use clap::{crate_authors, crate_version, App, Arg};
use futures::StreamExt as _;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio_vsock::{VsockListener, VsockAddr};

/// A simple Virtio socket server that uses Hyper to response to requests.
#[tokio::main]
async fn main() -> Result<(), ()> {
    let matches = App::new("test_server")
        .version(crate_version!())
        .author(crate_authors!())
        .about("Tokio Virtio socket test server")
        .arg(
            Arg::with_name("listen")
                .long("listen")
                .short("l")
                .help("Port to listen for Virtio connections")
                .required(true)
                .takes_value(true),
        )
        .get_matches();

    let listen_port = matches
        .value_of("listen")
        .expect("port is required")
        .parse::<u32>()
        .expect("port must be a valid integer");

    let addr = VsockAddr::new(libc::VMADDR_CID_ANY, listen_port);
    let listener = VsockListener::bind(addr).expect("unable to bind virtio listener");

    println!("Listening for connections on port: {}", listen_port);

    let mut incoming = listener.incoming();
    while let Some(result) = incoming.next().await {
        match result {
            Ok(mut stream) => {
                println!("Got connection ============");
                tokio::spawn(async move {
                    loop {
                        let mut buf = vec![0u8; 5000];
                        let len = stream.read(&mut buf).await.unwrap();

                        if len == 0 {
                            break;
                        }

                        buf.resize(len, 0);
                        println!("Got data: {:?}", &buf);
                        stream.write_all(&buf).await.unwrap();
                    }
                });
            }
            Err(e) => {
                println!("Got error: {:?}", e);
                return Err(());
            }
        }
    }

    Ok(())
}
