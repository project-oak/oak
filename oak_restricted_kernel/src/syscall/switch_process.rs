//
// Copyright 2024 The Project Oak Authors
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

use core::ffi::{c_size_t, c_ssize_t};

use oak_restricted_kernel_interface::Errno;

pub fn syscall_unstable_switch_proccess(pid: c_size_t) -> c_ssize_t {
    match unstable_switch_proccess(pid) {
        Ok(pid) => pid,
        Err(err) => err as isize,
    }
}

fn unstable_switch_proccess(pid: usize) -> Result<isize, Errno> {
    log::debug!("Switching to a different process (pid: {})", pid);
    // Safety: we're handling a syscall, so syscall handlers are registered.
    let prev_pid = unsafe { crate::syscall::GsData::get_current_pid() };
    // Safety: we're handling a syscall, the syscall entrypoint ensures that
    // updates to this value handled correctly.
    unsafe {
        crate::syscall::GsData::set_current_pid(pid)
            .inspect_err(|err| log::error!("failed to set pid: {:?}", err))
            .map_err(|_| Errno::EINVAL)?
    };
    isize::try_from(prev_pid)
        .inspect_err(|err| log::error!("failed to convert pid to isize. pid: {:?}", err))
        .map_err(|_| Errno::EINVAL)
}
