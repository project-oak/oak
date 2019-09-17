//
// Copyright 2019 The Project Oak Authors
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

#[macro_use]
extern crate log;
extern crate multinode_common;
extern crate oak;
extern crate oak_log;
extern crate protobuf;
extern crate serde;

use multinode_common::InternalMessage;
use protobuf::ProtobufEnum;
use std::io::Write;

#[no_mangle]
pub extern "C" fn oak_main() -> i32 {
    match std::panic::catch_unwind(|| {
        oak_log::init(log::Level::Debug, oak::channel_find("be_logging_port")).unwrap();
        oak::set_panic_hook();
        let in_handle = oak::channel_find("from_frontend");
        let out_handle = oak::channel_find("to_frontend");
        info!("backend node: in={}, out={}", in_handle, out_handle);

        let handles = vec![in_handle];
        let mut in_channel = oak::ReceiveChannelHalf::new(in_handle);
        let mut out_channel = oak::SendChannelHalf::new(out_handle);
        loop {
            match oak::wait_on_channels(&handles) {
                Ok(_ready_handles) => (),
                Err(err) => return err.value(),
            }
            let mut buf = Vec::<u8>::with_capacity(1024);
            let mut handles = Vec::with_capacity(1);
            in_channel.read_message(&mut buf, &mut handles).unwrap();
            if buf.is_empty() {
                info!("no pending message; poll again");
                continue;
            }

            let serialized_req = String::from_utf8(buf).unwrap();
            let internal_req: InternalMessage = serde_json::from_str(&serialized_req).unwrap();
            info!("received frontend request: {:?}", internal_req);

            let internal_rsp = InternalMessage {
                msg: internal_req.msg + "xxx",
            };

            let serialized_rsp = serde_json::to_string(&internal_rsp).unwrap();
            info!("send serialized message to frontend: {}", serialized_rsp);
            out_channel.write_all(&serialized_rsp.into_bytes()).unwrap();
        }
    }) {
        Ok(rc) => rc,
        Err(_) => oak::proto::oak_api::OakStatus::ERR_INTERNAL.value(),
    }
}
