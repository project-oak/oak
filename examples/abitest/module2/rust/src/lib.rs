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
extern crate abitest_common;
extern crate oak;
extern crate oak_log;
extern crate protobuf;
extern crate serde;

use abitest_common::InternalMessage;
use protobuf::ProtobufEnum;

// Backend node for channel testing.  This node listens for read channel handles
// arriving on the "from_frontend" channel, then in turn listens for JSON-serialized
// messages arriving on those read handles.  Any such messages are sent back to the
// frontend via the "to_frontend" channel, but in a slightly convoluted way: the
// response is written to a fresh channel, and the read handle for that new channel
// is what's sent back to the frontend.
#[no_mangle]
pub extern "C" fn oak_main() -> i32 {
    match std::panic::catch_unwind(|| {
        oak_log::init(
            log::Level::Debug,
            oak::WriteHandle {
                handle: oak::channel_find("be_logging_port"),
            },
        )
        .unwrap();
        oak::set_panic_hook();
        let in_handle = oak::channel_find("from_frontend");
        let out_handle = oak::channel_find("to_frontend");
        info!("backend node: in={}, out={}", in_handle, out_handle);

        let in_channel = oak::ReadHandle { handle: in_handle };
        let out_channel = oak::WriteHandle { handle: out_handle };
        // Wait on 1+N read handles (starting with N=0).
        let mut wait_handles = vec![in_channel];
        loop {
            let ready_status = match oak::wait_on_channels(&wait_handles) {
                Ok(ready_status) => ready_status,
                Err(err) => return err.value(),
            };
            // If there is a message on in_channel, it is expected to contain
            // a collection of read handles for future listening
            if ready_status[0] == oak::ChannelReadStatus::READ_READY {
                let mut buf = Vec::<u8>::with_capacity(16);
                let mut handles = Vec::with_capacity(5);
                oak::channel_read(in_channel, &mut buf, &mut handles);
                for handle in handles {
                    info!("add new handle {} to waiting set", handle);
                    wait_handles.push(oak::ReadHandle { handle });
                }
            }

            // All other channels expect to receive Serde-JSON serialized
            // messages.
            for i in 1..ready_status.len() {
                if ready_status[i] != oak::ChannelReadStatus::READ_READY {
                    continue;
                }
                info!(
                    "message available on waiting handle[{}]={:?}",
                    i, wait_handles[i]
                );
                let mut buf = Vec::<u8>::with_capacity(1024);
                let mut handles = Vec::with_capacity(1);
                oak::channel_read(wait_handles[i], &mut buf, &mut handles);
                if buf.is_empty() {
                    info!("no pending message; poll again");
                    continue;
                }

                let serialized_req = String::from_utf8(buf).unwrap();
                let internal_req: InternalMessage = serde_json::from_str(&serialized_req).unwrap();
                info!("received frontend request: {:?}", internal_req);

                // Create a new channel and write the response into it.
                let (new_write, new_read) = oak::channel_create().unwrap();
                let internal_rsp = InternalMessage {
                    msg: internal_req.msg + "xxx",
                };
                let serialized_rsp = serde_json::to_string(&internal_rsp).unwrap();
                info!(
                    "send serialized message to new channel {:?}: {}",
                    new_write, serialized_rsp
                );
                oak::channel_write(new_write, &serialized_rsp.into_bytes(), &[]);
                // Drop the write half now it has been written to.
                oak::channel_close(new_write.handle);

                // Send a copy of the read half of the new channel back to the frontend,
                // then close our handle to the read half.
                oak::channel_write(out_channel, &[], &[new_read.handle]);
                oak::channel_close(new_read.handle);
            }
        }
    }) {
        Ok(rc) => rc,
        Err(_) => oak::OakStatus::ERR_INTERNAL.value(),
    }
}
