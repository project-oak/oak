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

use nix::{
    errno::Errno,
    mount::{mount, umount, MsFlags},
    unistd::{execve, pivot_root},
};
use std::{ffi::CString, fs::create_dir};
use tar::{self, Archive};

pub static RAMFS_TMP_DIR: &str = "/ramfs";
static PIVOT_TMP_DIR: &str = "/initrd";

#[derive(Clone)]
pub struct Image {
    ramfs_tmp_dir: String,
}

impl Image {
    /// Prepares a new ramdrive.
    pub fn new(ramfs_tmp_dir: String) -> Result<Self, std::io::Error> {
        create_dir(ramfs_tmp_dir.as_str())?;
        mount::<str, str, str, str>(
            None,
            ramfs_tmp_dir.as_str(),
            Some("ramfs"),
            MsFlags::empty(),
            None,
        )?;
        Ok(Self { ramfs_tmp_dir })
    }

    /// Unpacks the buffer containing a TAR archive into the ramdrive.
    pub fn unpack(&self, data: &[u8]) -> Result<(), std::io::Error> {
        let mut archive = Archive::new(data);
        archive.unpack(self.ramfs_tmp_dir.as_str())
    }

    /// Switches the root filesystem to the ramdrive and runs `/sbin/init` from there.
    pub fn switch(self, init: &str) -> Result<!, Errno> {
        pivot_root(self.ramfs_tmp_dir.as_str(), PIVOT_TMP_DIR)?;
        umount(PIVOT_TMP_DIR)?;

        // On one hand, I feel like this function should be marked `unsafe` as this will
        // unconditionally switch over to the new executable (if it succeeds) without any
        // more Rust code executing. On the other hand, the return type is `!`, so you
        // shouldn't expect the control to return.
        execve::<CString, CString>(CString::new(init).unwrap().as_c_str(), &[], &[])?;
        unreachable!()
    }
}
