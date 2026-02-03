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

use std::{
    ffi::{CStr, CString},
    os::unix::prelude::OsStrExt,
    path::Path,
};

use anyhow::{Result, anyhow};
use bytes::Buf;
use nix::unistd::execve;
use tar::Archive;
use xz2::read::XzDecoder;

pub async fn extract<B: Buf>(buf: B, dst: &Path) -> Result<()> {
    let decoder = XzDecoder::new(buf.reader());
    let mut archive = Archive::new(decoder);
    archive.unpack(dst).map_err(|e| anyhow!(e))
}

pub fn switch<SE>(init: &str, env: &[SE]) -> Result<!>
where
    SE: AsRef<CStr>,
{
    // On one hand, I feel like this function should be marked `unsafe` as this will
    // unconditionally switch over to the new executable (if it succeeds) without
    // any more Rust code executing. On the other hand, the return type is `!`,
    // so you shouldn't expect the control to return.
    let args: Vec<CString> =
        std::env::args_os().map(|arg| CString::new(arg.as_bytes()).unwrap()).collect();
    execve(CString::new(init).unwrap().as_c_str(), &args[..], env)?;
    unreachable!()
}
