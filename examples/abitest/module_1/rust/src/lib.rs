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

use abitest_common::{InternalMessage, LOG_CONFIG_NAME};
use log::{error, info};
use std::collections::HashSet;

// Backend node for channel testing.  This node listens for read channel handles
// arriving on the "from_frontend" channel, then in turn listens for JSON-serialized
// messages arriving on those read handles.  Any such messages are sent back to the
// frontend via the "to_frontend" channel, but in a slightly convoluted way: the
// response is written to a fresh channel, and the read handle for that new channel
// is what's sent back to the frontend.
#[no_mangle]
pub extern "C" fn backend_oak_main(handle: u64) {
    let _ = std::panic::catch_unwind(|| {
        oak::set_panic_hook();

        match inner_main(handle) {
            Err(oak::OakStatus::ErrTerminated) => {
                info!("node terminated");
            }
            Err(s) => {
                error!("node failed: {:?}", s);
            }
            Ok(_) => {}
        }
    });
}

fn inner_main(in_handle: u64) -> Result<(), oak::OakStatus> {
    oak_log::init(log::Level::Debug, LOG_CONFIG_NAME).expect("Couldn't initialize logging node!");
    let in_channel = oak::ReadHandle {
        handle: oak::Handle::from_raw(in_handle),
    };

    // We expect a single empty message holding a reply channel to already
    // be waiting on the channel.
    let mut buf = Vec::<u8>::with_capacity(2);
    let mut handles = Vec::with_capacity(2);
    oak::channel_read(in_channel, &mut buf, &mut handles)?;
    if handles.len() != 1 {
        return Err(oak::OakStatus::ErrInternal);
    }
    let out_handle = handles[0];
    info!("backend node: in={:?}, out={:?}", in_channel, out_handle);

    let out_channel = oak::WriteHandle { handle: out_handle };
    // Wait on 1+N read handles (starting with N=0).
    let mut wait_handles = vec![in_channel];
    loop {
        let ready_status = oak::wait_on_channels(&wait_handles)?;
        // If there is a message on in_channel, it is expected to contain
        // a collection of read handles for future listening
        if ready_status[0] == oak::ChannelReadStatus::ReadReady {
            let mut buf = Vec::<u8>::with_capacity(16);
            let mut handles = Vec::with_capacity(5);
            oak::channel_read(in_channel, &mut buf, &mut handles)?;
            for handle in handles {
                info!("add new handle {:?} to waiting set", handle);
                wait_handles.push(oak::ReadHandle { handle });
            }
        }

        // All other channels expect to receive Serde-JSON serialized
        // messages.
        let mut orphaned_handles = HashSet::new();
        for i in 1..ready_status.len() {
            if ready_status[i] != oak::ChannelReadStatus::ReadReady {
                if ready_status[i] == oak::ChannelReadStatus::Orphaned {
                    let orphan_handle = wait_handles[i].handle;
                    orphaned_handles.insert(orphan_handle);
                    info!("close orphaned channel[{}]={:?}", i, orphan_handle);
                    oak::channel_close(orphan_handle)?;
                }
                continue;
            }
            info!(
                "message available on waiting handle[{}]={:?}",
                i, wait_handles[i]
            );
            let mut buf = Vec::<u8>::with_capacity(1024);
            let mut handles = Vec::with_capacity(1);

            oak::channel_read(wait_handles[i], &mut buf, &mut handles).or_else(|err| {
                if err == oak::OakStatus::ErrChannelClosed || err == oak::OakStatus::ErrChannelEmpty
                {
                    // Multiple backend Nodes are attempting to read the message from
                    // the channel, so it's entirely possible that one of them has
                    // emptied the channel since the wait_on_channels() call (and that the frontend
                    // Node has subsequently closed the channel).
                    info!("message on channel {:?} stolen elsewhere!", wait_handles[i]);
                    Ok(())
                } else {
                    Err(err)
                }
            })?;
            if buf.is_empty() {
                info!("no pending message; poll again");
                continue;
            }

            let serialized_req = String::from_utf8(buf).unwrap();
            let internal_req: InternalMessage = serde_json::from_str(&serialized_req).unwrap();
            info!("received frontend request: {:?}", internal_req);

            // Create a new channel and write the response into it.
            let (new_write, new_read) = oak::channel_create()?;
            let internal_rsp = InternalMessage {
                msg: internal_req.msg + "xxx",
            };
            let serialized_rsp = serde_json::to_string(&internal_rsp).unwrap();
            info!(
                "send serialized message to new channel {:?}: {}",
                new_write, serialized_rsp
            );
            oak::channel_write(new_write, &serialized_rsp.into_bytes(), &[])?;
            // Drop the write half now it has been written to.
            oak::channel_close(new_write.handle)?;

            // Send a copy of the read half of the new channel back to the frontend,
            // then close our handle to the read half.
            oak::channel_write(out_channel, &[], &[new_read.handle])?;
            oak::channel_close(new_read.handle)?;
        }

        // Drop any orphaned channels from the wait set now iteration is done.
        wait_handles.retain(|&h| !orphaned_handles.contains(&h.handle));
    }
}

// Exported entrypoint that has the wrong signature for a main Oak
// entrypoint; just used for testing
#[no_mangle]
pub extern "C" fn backend_fake_main(_handle: u64, _another: u64) {
    panic!("reached backend_fake_main!");
}
