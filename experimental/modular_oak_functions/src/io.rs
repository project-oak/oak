//
// Copyright 2022 The Project Oak Authors
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

use crate::demux::Demux;

pub struct IoListener {
    demux: Demux,
}

impl IoListener {
    pub fn new(demux: Demux) -> Self {
        Self { demux }
    }

    pub fn listen(&self) -> anyhow::Result<()> {
        eprintln!("starting");
        // In a real implementation it would listen on an IO stream here handle the incoming
        // frames, but for now we just create a fake frame, send it into the rest of the system and
        // print the response.
        let response = self.demux.handle_frame(b"test")?;
        println!("response: {}", std::str::from_utf8(&response)?);
        Ok(())
    }
}
