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

use anyhow::{anyhow, Context, Result};
use nix::unistd::execv;
use std::{ffi::CString, os::unix::prelude::OsStrExt, path::Path};
use tar::Archive;
use xz2::read::XzDecoder;

use crate::client::LauncherClient;

pub async fn load(client: &mut LauncherClient, dst: &Path) -> Result<()> {
    let buf = client
        .get_oak_system_image()
        .await
        .context("fetching system image")?;
    let decoder = XzDecoder::new(&buf[..]);
    let mut archive = Archive::new(decoder);
    archive.unpack(dst).map_err(|e| anyhow!(e))
}

pub fn switch(init: &str) -> Result<!> {
    // On one hand, I feel like this function should be marked `unsafe` as this will
    // unconditionally switch over to the new executable (if it succeeds) without any
    // more Rust code executing. On the other hand, the return type is `!`, so you
    // shouldn't expect the control to return.
    let args: Vec<CString> = std::env::args_os()
        .map(|arg| CString::new(arg.as_bytes()).unwrap())
        .collect();
    execv(CString::new(init).unwrap().as_c_str(), &args[..])?;
    unreachable!()
}
