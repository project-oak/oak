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

use std::{
    fs,
    net::{IpAddr, Ipv4Addr, SocketAddr},
};

use clap::Parser;
use oak_functions_service::wasm::wasmtime::WasmtimeHandler;
use oak_functions_standalone::{serve, OakFunctionsSessionArgs};
use oak_proto_rust::oak::functions::{
    config::ApplicationConfig, InitializeRequest, LookupDataChunk,
};
use prost::Message;
use tokio::net::TcpListener;
use tokio_stream::wrappers::TcpListenerStream;

const OAK_FUNCTIONS_STANDALONE_PORT: u16 = 8080;

#[global_allocator]
static ALLOCATOR: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

#[derive(Parser, Debug)]
struct Args {
    // The wasm_path must be specified in the BUILD data dependency
    // TODO: b/424407998 - Have wasm_path point to content addressable storage
    #[arg(short, long, default_value = "usr/local/bin/key_value_lookup.wasm")]
    wasm_path: String,

    #[arg(short, long, default_value = "usr/local/bin/fake_weather_data.binarypb")]
    lookup_data_path: String,
}

// Parses lookup data from the `lookup_data_path` into a vector
fn parse_lookup_data_chunk(lookup_data_path: String) -> LookupDataChunk {
    let lookup_data_buffer =
        fs::read(lookup_data_path).expect("failed to read lookup data from file");
    LookupDataChunk::decode(lookup_data_buffer.as_slice()).unwrap()
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    if args.wasm_path.is_empty() {
        panic!("--wasm_path must be specified")
    }

    let mut lookup_data_option: Option<LookupDataChunk> = None;

    if !args.lookup_data_path.is_empty() {
        println!("reading LookupDataChunk from: {}", args.lookup_data_path);
        lookup_data_option = Some(parse_lookup_data_chunk(args.lookup_data_path));
    }

    // This is a hack to get _some_ logging out of the binary, and should be
    // replaced with proper OTLP logging (or logging to journald, or something) in
    // the not too distant future. Debug logging is also only enabled for the
    // `oak_functions_service` module as Tonic tends to be rather chatty if
    // you enable debug logs everywhere; also, this could end up in a feedback
    // loop as if we create a RPC do do the debug logging, it'll mean the RPC
    // itself will generate more debug logs, which in turn will be sent via a
    // RPC, and the cycle continues.
    env_logger::builder()
        .filter_module("oak_functions_service", log::LevelFilter::Debug)
        .try_init()?;

    let application_config = ApplicationConfig::default();
    let wasmtime_config = application_config.wasmtime_config.unwrap_or_default();

    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), OAK_FUNCTIONS_STANDALONE_PORT);

    let oak_functions_session_args = OakFunctionsSessionArgs {
        wasm_initialization: InitializeRequest {
            constant_response_size: 100, // This value is ultimately ignored.
            wasm_module: fs::read(args.wasm_path).expect("failed to read wasm module"),
        },
        lookup_data: lookup_data_option,
    };

    let server_handle = {
        let listener = TcpListener::bind(addr).await?;
        serve::<WasmtimeHandler>(
            Box::new(TcpListenerStream::new(listener)),
            wasmtime_config,
            oak_functions_session_args,
        )
    };

    println!("Listening on Address: {}", addr);

    Ok(server_handle.await?)
}
