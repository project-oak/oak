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

use strum::{Display, FromRepr};

/// Possible error values returned by Oak Restricted Kernel syscalls.
///
/// In general, the errors and their associated values are inpired by and look
/// similar to the Linux/POSIX ABI, but we make no claims about adhering to the
/// behaviour, or specification, of either of those.
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Display, Eq, FromRepr, PartialEq)]
#[repr(isize)]
#[non_exhaustive]
pub enum Errno {
    /// Input/output error
    EIO = -5,
    /// Bad file descriptor
    EBADF = -9,
    /// Cannot allocate memory
    ENOMEM = -12,
    /// Bad address
    EFAULT = -14,
    /// Invalid argument
    EINVAL = -22,
    /// Function not implemented
    ENOSYS = -38,
}
